import BB.InvariantState

/-!
# Exact periodic states, with arbitrary surviving supports

A finite orbit average is an actual invariant probability measure. The proven
invariant-measure bound and its equality classification therefore apply even
when the orbit lies on a proper face. The exponential average of logarithmic
growth is shown equal to the manuscript's product formula.
-/

namespace BB
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal

section FiniteOrbit
variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

def finiteOrbitMeasure (T : X → X) (x : X) (p : ℕ) : Measure X :=
  (p : ℝ≥0∞)⁻¹ • ∑ k in Finset.range p, Measure.dirac (T^[k] x)

lemma finite_orbit_probability (T : X → X) (x : X) (p : ℕ) (hp : 0 < p) :
    IsProbabilityMeasure (finiteOrbitMeasure T x p) := by
  constructor
  simp only [finiteOrbitMeasure, Measure.smul_apply, Measure.finset_sum_apply,
    measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne' : (p : ℝ≥0∞) ≠ 0) (by simp)

lemma sum_range_shift_of_return {M : Type*} [AddCommMonoid M]
    (f : ℕ → M) (p : ℕ) (hp : 0 < p) (hreturn : f p = f 0) :
    (∑ k in Finset.range p, f (k + 1)) = ∑ k in Finset.range p, f k := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp.ne'
  rw [Finset.sum_range_succ (fun k => f (k + 1)), Finset.sum_range_succ' f, hreturn]

lemma map_sum_range_dirac (T : X → X) (hT : Measurable T) (x : X) (p : ℕ) :
    Measure.map T (∑ k in Finset.range p, Measure.dirac (T^[k] x)) =
      ∑ k in Finset.range p, Measure.dirac (T^[k + 1] x) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, Measure.map_add _ _ hT, ih,
      Measure.map_dirac hT, Finset.sum_range_succ]
    rw [Function.iterate_succ_apply']

lemma finite_orbit_measure_preserving (T : X → X) (hT : Measurable T)
    (x : X) (p : ℕ) (hp : 0 < p) (hreturn : T^[p] x = x) :
    MeasurePreserving T (finiteOrbitMeasure T x p) (finiteOrbitMeasure T x p) := by
  refine ⟨hT, ?_⟩
  rw [finiteOrbitMeasure, Measure.map_smul, map_sum_range_dirac T hT x p]
  congr 1
  apply sum_range_shift_of_return (fun k => Measure.dirac (T^[k] x)) p hp
  simpa using congrArg Measure.dirac hreturn

lemma ae_sum_range_dirac_iff (v : ℕ → X) (p : ℕ) (P : X → Prop) :
    (∀ᵐ y ∂(∑ k in Finset.range p, Measure.dirac (v k)), P y) ↔
      ∀ k < p, P (v k) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ae_add_measure_iff, ih, ae_dirac_eq]
    simp only [Filter.eventually_pure]
    constructor
    · rintro ⟨h, hp⟩ k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact h k hk
      · exact hp
    · intro h
      exact ⟨fun k hk => h k (Nat.lt_succ_of_lt hk), h p (Nat.lt_succ_self p)⟩

lemma finite_orbit_ae_iff (T : X → X) (x : X) (p : ℕ) (P : X → Prop) :
    (∀ᵐ y ∂finiteOrbitMeasure T x p, P y) ↔ ∀ k < p, P (T^[k] x) := by
  rw [finiteOrbitMeasure, Measure.ae_smul_measure_iff (by simp), ae_sum_range_dirac_iff]

lemma integrable_dirac_any (f : X → ℝ) (x : X) : Integrable f (Measure.dirac x) :=
  (integrable_const (f x)).congr (ae_eq_dirac f).symm

lemma finite_orbit_integrable (T : X → X) (x : X) (p : ℕ) (hp : 0 < p) (f : X → ℝ) :
    Integrable f (finiteOrbitMeasure T x p) := by
  apply Integrable.smul_measure
  · exact integrable_finset_sum_measure.mpr (fun k _ => integrable_dirac_any f (T^[k] x))
  · exact ENNReal.inv_ne_top.mpr (by exact_mod_cast hp.ne')

lemma finite_orbit_integral (T : X → X) (x : X) (p : ℕ) (f : X → ℝ) :
    (∫ y, f y ∂finiteOrbitMeasure T x p) =
      (∑ k in Finset.range p, f (T^[k] x)) / (p : ℝ) := by
  rw [finiteOrbitMeasure, integral_smul_measure,
    integral_finset_sum_measure (fun k _ => integrable_dirac_any f (T^[k] x))]
  simp [integral_dirac, ENNReal.toReal_inv, smul_eq_mul, div_eq_mul_inv, mul_comm]

end FiniteOrbit


section SpectralPeriodic
variable {ι : Type*} [Fintype ι]

/-- The manuscript's per-step norm factor over one exact period. -/
def periodicNormFactor (lam : ι → ℝ) (χ : SpectralState ι) (p : ℕ) : ℝ :=
  (∏ k in Finset.range p, stateGrowthSq lam ((spectralMap lam)^[k] χ)) ^
    (1 / (2 * (p : ℝ)))

lemma periodic_factor_eq_exp_average (lam : ι → ℝ) (χ : SpectralState ι)
    (p : ℕ) (hp : 0 < p)
    (hregular : ∀ k < p, 0 < stateGrowthSq lam ((spectralMap lam)^[k] χ)) :
    periodicNormFactor lam χ p =
      Real.exp ((∑ k in Finset.range p, Real.log (stateGrowth lam ((spectralMap lam)^[k] χ))) /
        (p : ℝ)) := by
  have hprod : 0 < ∏ k in Finset.range p, stateGrowthSq lam ((spectralMap lam)^[k] χ) :=
    Finset.prod_pos (fun k hk => hregular k (Finset.mem_range.mp hk))
  have hs : (∑ k in Finset.range p, Real.log (stateGrowth lam ((spectralMap lam)^[k] χ))) =
      (∑ k in Finset.range p, Real.log (stateGrowthSq lam ((spectralMap lam)^[k] χ))) / 2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    exact Real.log_sqrt (hregular k (Finset.mem_range.mp hk)).le
  rw [periodicNormFactor, Real.rpow_def_of_pos hprod,
    Real.log_prod _ _ (fun k hk => (hregular k (Finset.mem_range.mp hk)).ne'), hs]
  congr 1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  field_simp

/-- Periodic average bound with no positivity assumption on individual
spectral coordinates. The orbit may lie on any proper face. -/
lemma spectral_periodic_full_average_le (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (χ : SpectralState ι)
    (p : ℕ) (hp : 0 < p) (hreturn : (spectralMap lam)^[p] χ = χ)
    (hregular : ∀ k < p, 0 < stateGrowthSq lam ((spectralMap lam)^[k] χ)) :
    (∑ k in Finset.range p, Real.log (stateGrowth lam ((spectralMap lam)^[k] χ))) /
      (p : ℝ) ≤ Real.log (rate a b) := by
  let μ := finiteOrbitMeasure (spectralMap lam) χ p
  letI : IsProbabilityMeasure μ := finite_orbit_probability (spectralMap lam) χ p hp
  have hT := finite_orbit_measure_preserving (spectralMap lam)
    (spectral_map_measurable lam a ha (fun i => (hlam i).1)) χ p hp hreturn
  have hr : ∀ᵐ x ∂μ, 0 < stateGrowthSq lam x :=
    (finite_orbit_ae_iff (spectralMap lam) χ p _).mpr hregular
  have hf := finite_orbit_integrable (spectralMap lam) χ p hp (fun x => Real.log (stateGrowth lam x))
  have hb := spectral_state_invariant_bound lam a b ha hlam μ hT hr hf
  rw [finite_orbit_integral] at hb
  exact hb

lemma spectral_periodic_full_average_eq_iff (lam : ι → ℝ) (hinj : Function.Injective lam)
    (lo hi : ι) (hne : lo ≠ hi) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (χ : SpectralState ι) (p : ℕ) (hp : 0 < p)
    (hreturn : (spectralMap lam)^[p] χ = χ)
    (hregular : ∀ k < p, 0 < stateGrowthSq lam ((spectralMap lam)^[k] χ)) :
    (∑ k in Finset.range p, Real.log (stateGrowth lam ((spectralMap lam)^[k] χ))) /
      (p : ℝ) = Real.log (rate a b) ↔
    ∀ k < p, (spectralMap lam)^[k] χ = balancedSpectralState lo hi hne := by
  let μ := finiteOrbitMeasure (spectralMap lam) χ p
  letI : IsProbabilityMeasure μ := finite_orbit_probability (spectralMap lam) χ p hp
  constructor
  · intro he
    have hT := finite_orbit_measure_preserving (spectralMap lam)
      (spectral_map_measurable lam a ha (fun i => (hlam i).1)) χ p hp hreturn
    have hr : ∀ᵐ x ∂μ, 0 < stateGrowthSq lam x :=
      (finite_orbit_ae_iff (spectralMap lam) χ p _).mpr hregular
    have hf := finite_orbit_integrable (spectralMap lam) χ p hp (fun x => Real.log (stateGrowth lam x))
    have hmax : (∫ x, Real.log (stateGrowth lam x) ∂μ) = Real.log (rate a b) := by
      rw [finite_orbit_integral]
      exact he
    have hμ := spectral_state_unique_maximizer lam hinj lo hi hne a b ha hab hlo hhi hlam
      μ hT hr hf hmax
    apply (finite_orbit_ae_iff (spectralMap lam) χ p (fun x => x = balancedSpectralState lo hi hne)).mp
    change ∀ᵐ x ∂μ, x = balancedSpectralState lo hi hne
    rw [hμ, ae_dirac_eq]
    simp
  · intro hfixed
    have hg : stateGrowth lam (balancedSpectralState lo hi hne) = rate a b := by
      simpa only [hlo, hhi] using balanced_growth lam lo hi hne (hlo ▸ ha) (by simpa [hlo, hhi])
    have hs : (∑ k in Finset.range p, Real.log (stateGrowth lam ((spectralMap lam)^[k] χ))) =
        (p : ℝ) * Real.log (rate a b) := by
      calc
        _ = ∑ _k in Finset.range p, Real.log (rate a b) :=
          Finset.sum_congr rfl (fun k hk => by rw [hfixed k (Finset.mem_range.mp hk), hg])
        _ = _ := by simp
    rw [hs]
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
    field_simp

/-- Full periodic product bound, in exactly the manuscript's product convention. -/
lemma spectral_periodic_factor_le (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (χ : SpectralState ι)
    (p : ℕ) (hp : 0 < p) (hreturn : (spectralMap lam)^[p] χ = χ)
    (hregular : ∀ k < p, 0 < stateGrowthSq lam ((spectralMap lam)^[k] χ)) :
    periodicNormFactor lam χ p ≤ rate a b := by
  rw [periodic_factor_eq_exp_average lam χ p hp hregular]
  calc
    _ ≤ Real.exp (Real.log (rate a b)) := Real.exp_le_exp.mpr
      (spectral_periodic_full_average_le lam a b ha hlam χ p hp hreturn hregular)
    _ = rate a b := Real.exp_log (rate_pos ha hab)

/-- Equality occurs exactly when every orbit state is the balanced endpoint
fixed state. Distinct spectral coordinates are explicit for this classification. -/
lemma spectral_periodic_factor_eq_iff (lam : ι → ℝ) (hinj : Function.Injective lam)
    (lo hi : ι) (hne : lo ≠ hi) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (χ : SpectralState ι) (p : ℕ) (hp : 0 < p)
    (hreturn : (spectralMap lam)^[p] χ = χ)
    (hregular : ∀ k < p, 0 < stateGrowthSq lam ((spectralMap lam)^[k] χ)) :
    periodicNormFactor lam χ p = rate a b ↔
      ∀ k < p, (spectralMap lam)^[k] χ = balancedSpectralState lo hi hne := by
  rw [periodic_factor_eq_exp_average lam χ p hp hregular,
    ← Real.exp_log (rate_pos ha hab), Real.exp_eq_exp]
  exact spectral_periodic_full_average_eq_iff lam hinj lo hi hne a b ha hab hlo hhi hlam
    χ p hp hreturn hregular

end SpectralPeriodic

end
end BB
