import BB.BorelSpectrum
import BB.BorelConjugacy
import BB.BorelEigen
import BB.BorelRateTransfer
import BB.PositiveSquareRoot
import BB.HilbertErrorObjective

/-!
# The complete bounded Borel weighted Hilbert corollary

The weight is defined on the actual real spectrum. Its operator and commuting
boundedly invertible square root are constructed. Intrinsic active support,
root factors, the exact transfer of any given BB1 prefactor, both directions of
the uniform rate threshold, and exact weighted eigenspace trajectories follow.
-/

noncomputable section
namespace BB
open MeasureTheory Set
open scoped Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)
  (Ψ : spectrum ℝ A → ℝ) (hΨ : Measurable Ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) (hΨbounds : ∀ t, l ≤ Ψ t ∧ Ψ t ≤ u)

/-- A genuine boundedly invertible square root of the actual Borel operator. -/
def spectralBorelSquareRoot : E →L[ℝ] E :=
  (positive_operator_square_root_exists
    (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)
    (spectral_borel_operator_symmetric A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)
    l u hl hlu (spectral_borel_operator_bounds A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)).choose

theorem spectral_borel_square_root_properties :
    let W := spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
    let S := spectralBorelSquareRoot A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
    S.toLinearMap.IsSymmetric ∧ W = S.comp S ∧
      (∀ x, Real.sqrt l * ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ Real.sqrt u * ‖x‖) ∧
      IsUnit S ∧ (∀ x, S (A x) = A (S x)) := by
  have h := (positive_operator_square_root_exists
    (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)
    (spectral_borel_operator_symmetric A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)
    l u hl hlu (spectral_borel_operator_bounds A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)).choose_spec
  refine ⟨h.1, h.2.1, h.2.2.2.1, h.2.2.2.2.1, ?_⟩
  apply h.2.2.2.2.2 A
  intro x
  exact congrArg (fun T : E →L[ℝ] E => T x)
    (spectral_borel_operator_commute A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).eq

lemma spectral_borel_square_root_ne_zero (x : E) (hx : x ≠ 0) :
    spectralBorelSquareRoot A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x ≠ 0 := by
  have h := spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  exact norm_lower_operator_ne_zero _ _ (Real.sqrt_pos.mpr hl) (fun z => (h.2.2.1 z).1) x hx

/-- Every nonzero-vector weighted quotient is positive. -/
theorem spectral_borel_step_positive (ha : 0 < a) (hab : a ≤ b) (x : E) (hx : x ≠ 0) :
    0 < operatorWeightedBB A.toLinearMap
      (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap x := by
  obtain ⟨hS, hsq, _hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  rw [operator_weighted_quotient_conjugacy A _ _ hS hsq hcomm]
  exact (positive_operator_bb1_bounds A a b ha (ha.trans_le hab) hbounds _
    (spectral_borel_square_root_ne_zero A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x hx)).1

/-- The source's explicit lower bound for the weighted denominator. -/
theorem spectral_borel_product_lower (ha : 0 ≤ a) (x : E) :
    l * a * ‖x‖^2 ≤
      ⟪spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds (A x), x⟫ := by
  obtain ⟨hS, hsq, _hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  let W := spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  let S := spectralBorelSquareRoot A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  change W = S.comp S at hsq
  change ∀ z, S (A z) = A (S z) at hcomm
  have hnorm : l * ‖x‖^2 ≤ ‖S x‖^2 := by
    calc
      l * ‖x‖^2 ≤ ⟪x, W x⟫ :=
        (spectral_borel_operator_bounds A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x).1
      _ = ⟪S x, S x⟫ := by rw [hsq]; exact (hS x (S x)).symm
      _ = ‖S x‖^2 := real_inner_self_eq_norm_sq _
  have heq : ⟪W (A x), x⟫ = ⟪S x, A (S x)⟫ := by
    calc
      ⟪W (A x), x⟫ = ⟪S (A x), S x⟫ := by rw [hsq]; exact hS _ _
      _ = ⟪A (S x), S x⟫ := by rw [hcomm]
      _ = ⟪S x, A (S x)⟫ := real_inner_comm _ _
  calc
    l * a * ‖x‖^2 = a * (l * ‖x‖^2) := by ring
    _ ≤ a * ‖S x‖^2 := mul_le_mul_of_nonneg_left hnorm ha
    _ ≤ ⟪S x, A (S x)⟫ := (hbounds (S x)).1
    _ = _ := heq.symm

/-- The exact normalized spectral-density formula for the constructed source-domain square root. -/
theorem spectral_borel_square_root_probability (x : E) (hx : x ≠ 0) :
    (operatorSpectralProbability A hA a b hbounds
      (spectralBorelSquareRoot A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x)
      (spectral_borel_square_root_ne_zero A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x hx) :
      Measure (Icc a b)) =
      normalizedReweight (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))
        (fun t => ENNReal.ofReal (spectrumIntervalWeight A a b Ψ l t)) := by
  obtain ⟨hS, hsq, _hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  exact borel_square_root_spectral_probability A hA a b hbounds
    (spectrumIntervalWeight A a b Ψ l) (spectrumIntervalWeight_measurable A a b Ψ hΨ l)
    l u hl hlu (fun t => extendSpectrumWeight_bounds A Ψ l u hlu hΨbounds (t : ℝ))
    _ hS hsq hcomm x hx _

/-- The actual active spectral support is unchanged by the constructed square root. -/
theorem spectral_borel_active_support (x : E) (hx : x ≠ 0) :
    operatorActiveSupport A hA a b hbounds
      (spectralBorelSquareRoot A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x)
      (spectral_borel_square_root_ne_zero A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x hx) =
      operatorActiveSupport A hA a b hbounds x hx := by
  obtain ⟨hS, hsq, _hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  apply congrArg (fun T : Set (Icc a b) => Subtype.val '' T)
  exact borel_square_root_support A hA a b hbounds (spectrumIntervalWeight A a b Ψ l)
    (spectrumIntervalWeight_measurable A a b Ψ hΨ l) l u hl hlu
    (fun t => extendSpectrumWeight_bounds A Ψ l u hlu hΨbounds (t : ℝ))
    _ hS hsq hcomm x hx _

/-- Arbitrary positive first steps satisfy the intrinsic active-support root bound. -/
theorem spectral_borel_rootFactor_le (ha : 0 < a) (hab : a ≤ b) (g : ℕ → E) (α₀ : ℝ)
    (hg : IsOperatorDelayedTrajectory A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap) g α₀) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤
      rate (sInf (operatorActiveSupport A hA a b hbounds (g 0) hg.initial_ne))
        (sSup (operatorActiveSupport A hA a b hbounds (g 0) hg.initial_ne)) ∧
      rate (sInf (operatorActiveSupport A hA a b hbounds (g 0) hg.initial_ne))
        (sSup (operatorActiveSupport A hA a b hbounds (g 0) hg.initial_ne)) ≤ rate a b := by
  obtain ⟨hS, hsq, hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  let S := spectralBorelSquareRoot A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  have hS0 := spectral_borel_square_root_ne_zero A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds (g 0) hg.initial_ne
  refine ⟨?_, operator_active_rate_le_global A hA a b ha hbounds (g 0) hg.initial_ne⟩
  rw [hilbert_weighted_root_conjugacy A _ S hA hS hsq hcomm a b (Real.sqrt l) (Real.sqrt u)
    ha hab (Real.sqrt_pos.mpr hl) (Real.sqrt_pos.mpr (hl.trans_le hlu)) hbounds
    (fun x => (hnorm x).1) (fun x => (hnorm x).2) g hg.initial_ne hg.update]
  have hfirst : S (g 1) = operatorGradientStep A.toLinearMap α₀ (S (g 0)) := by
    rw [hg.first, commuting_operator_step A S hcomm]
  have hactive := operator_active_support_rootFactor_le A hA a b ha hbounds
    (fun n => S (g n)) hS0 α₀ hfirst
    (operator_weighted_orbit_conjugacy A _ S hS hsq hcomm g hg.update)
  rw [spectral_borel_active_support A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds] at hactive
  exact hactive

/-- Transfer of any already valid BB1 constant, with exactly sqrt(ψ₊/ψ₋). -/
theorem spectral_borel_given_envelope (C γ : ℝ) (hγ : 0 < γ)
    (henv : ∀ (v : ℕ → E), v 0 ≠ 0 →
      v 1 = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (v 0)) (v 0) →
      (∀ n, v (n+2) = operatorGradientStep A.toLinearMap
        (operatorBB1 A.toLinearMap (v n)) (v (n+1))) →
      ∀ n, ‖v n‖ ≤ C * γ^n * ‖v 0‖)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap (g n)) (g (n+1))) :
    ∀ n, ‖g n‖ ≤ Real.sqrt (u/l) * C * γ^n * ‖g 0‖ := by
  obtain ⟨hS, hsq, hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  simpa only [Real.sqrt_div (hl.le.trans hlu)] using
    hilbert_weighted_given_envelope_transfer A _ _ hS hsq hcomm (Real.sqrt l) (Real.sqrt u) C γ
      (Real.sqrt_pos.mpr hl) hγ (fun x => (hnorm x).1) (fun x => (hnorm x).2)
      henv g hg0 hfirst hupdate

/-- Bounded inverse conjugacy also transfers every uniform lower obstruction. -/
theorem spectral_borel_uniform_rates_eq :
    operatorMatchedUniformRates A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap) =
      operatorMatchedUniformRates A.toLinearMap (operatorBB1 A.toLinearMap) := by
  obtain ⟨hS, hsq, hnorm, hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  exact weighted_matched_uniform_rates_eq A _ _ hS hsq hcomm (Real.sqrt l) (Real.sqrt u)
    (Real.sqrt_pos.mpr hl) (Real.sqrt_pos.mpr (hl.trans_le hlu))
    (fun x => (hnorm x).1) (fun x => (hnorm x).2) hunit

/-- The exact infimum statement, including continuous spectra without endpoint eigenvectors. -/
theorem spectral_borel_uniform_infimum (ha : 0 < a) (hab : a ≤ b)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    sInf (operatorMatchedUniformRates A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap)) = rate a b := by
  rw [spectral_borel_uniform_rates_eq A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds]
  exact hilbert_operator_uniform_infimum A hA a b ha hab hbounds haspec hbspec

/-- Actual error and quadratic-objective root factors for all bounded Borel weights. -/
theorem spectral_borel_error_objective_factors (ha : 0 < a) (hab : a ≤ b)
    (g e : ℕ → E) (hg0 : g 0 ≠ 0) (hgradient : ∀ n, g n = A (e n))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = rootFactor (fun n => ‖g n‖/‖g 0‖) ∧
      rootFactor (fun n => operatorObjective A.toLinearMap (e n)/operatorObjective A.toLinearMap (e 0)) =
        (rootFactor (fun n => ‖g n‖/‖g 0‖))^2 := by
  obtain ⟨hS, hsq, hnorm, _hunit, hcomm⟩ :=
    spectral_borel_square_root_properties A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
  exact hilbert_weighted_error_objective_factors A _ _ hA hS hsq hcomm a b (Real.sqrt l)
    ha hab (Real.sqrt_pos.mpr hl) hbounds (fun x => (hnorm x).1) g e hg0 hgradient hupdate

/-- The source-domain Borel operator has the correct value on every eigenspace. -/
theorem spectral_borel_operator_eigenvector (r : spectrum ℝ A) (x : E)
    (hx : A x = (r : ℝ) • x) :
    spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x = Ψ r • x := by
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hn : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx0)
    have hb := hbounds x
    rw [hx, inner_smul_right, real_inner_self_eq_norm_sq] at hb
    have hr : (r : ℝ) ∈ Icc a b :=
      ⟨(mul_le_mul_right hn).mp hb.1, (mul_le_mul_right hn).mp hb.2⟩
    have he := borel_weight_operator_eigenvector A hA a b hbounds (spectrumIntervalWeight A a b Ψ l)
      (spectrumIntervalWeight_measurable A a b Ψ hΨ l) l u hl hlu
      (fun t => extendSpectrumWeight_bounds A Ψ l u hlu hΨbounds (t : ℝ)) ⟨r, hr⟩ x hx
    change spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x =
      extendSpectrumWeight A Ψ l (r : ℝ) • x at he
    rw [extendSpectrumWeight_on_spectrum] at he
    exact he

/-- Exact Ψ-balanced endpoint trajectories for arbitrary source-domain Borel weights. -/
theorem spectral_borel_endpoint_matched_orbit (r s : spectrum ℝ A)
    (hr : 0 < (r : ℝ)) (hrs : (r : ℝ) < s) (p q : E)
    (hp : A p = (r : ℝ) • p) (hq : A q = (s : ℝ) • q)
    (hp0 : p ≠ 0) (hbal : Ψ r * ‖p‖^2 = Ψ s * ‖q‖^2) :
    let W := spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds
    let g := hilbertEndpointOrbit (r : ℝ) (s : ℝ) p q
    g 0 ≠ 0 ∧ 0 < operatorWeightedBB A.toLinearMap W.toLinearMap (g 0) ∧
      g 1 = operatorGradientStep A.toLinearMap (operatorWeightedBB A.toLinearMap W.toLinearMap (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep A.toLinearMap
        (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate (r : ℝ) (s : ℝ))^n * ‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖/‖g 0‖) = rate (r : ℝ) (s : ℝ) := by
  exact hilbert_weighted_endpoint_matched_orbit A.toLinearMap _ hA (r : ℝ) (s : ℝ)
    (Ψ r) (Ψ s) hr hrs (hl.trans_le (hΨbounds r).1) p q hp hq
    (spectral_borel_operator_eigenvector A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds r p hp)
    (spectral_borel_operator_eigenvector A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds s q hq) hp0 hbal

end BB
