import BB.HilbertProbability

/-!
# The actual balanced endpoint probability measure

The maximizing state is built from two Dirac measures. Endpoint concentration
and the midpoint mean identify it uniquely; its actual normalized measure map
and growth are computed exactly.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {K : Type*} [MeasurableSpace K]

def balancedProbability (xa xb : K) : ProbabilityMeasure K :=
  ⟨(2 : ℝ≥0∞)⁻¹ • (Measure.dirac xa + Measure.dirac xb), by
    constructor
    simp only [Measure.smul_apply, Measure.add_apply, measure_univ, smul_eq_mul]
    norm_num
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩

variable [MeasurableSingletonClass K]

theorem balanced_probability_integral (xa xb : K) (f : K → ℝ) :
    (∫ x, f x ∂(balancedProbability xa xb : Measure K)) = (f xa + f xb) / 2 := by
  have ha : Integrable f (Measure.dirac xa) :=
    (integrable_const (f xa)).congr (ae_eq_dirac f).symm
  have hb : Integrable f (Measure.dirac xb) :=
    (integrable_const (f xb)).congr (ae_eq_dirac f).symm
  change (∫ x, f x ∂((2 : ℝ≥0∞)⁻¹ • (Measure.dirac xa + Measure.dirac xb))) = _
  rw [integral_smul_measure, integral_add_measure ha hb]
  simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_ofNat, smul_eq_mul]
  ring

variable [TopologicalSpace K] [CompactSpace K] [BorelSpace K]
  [HasOuterApproxClosed K]

theorem probability_eq_balanced_of_endpoints_mean (ν : ProbabilityMeasure K)
    (lam : C(K,ℝ)) (hinj : Function.Injective lam) (xa xb : K)
    (a b : ℝ) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b)
    (hend : ∀ᵐ x ∂(ν : Measure K), lam x = a ∨ lam x = b)
    (hmean : (∫ x, lam x ∂(ν : Measure K)) = (a + b) / 2) :
    ν = balancedProbability xa xb := by
  apply probability_functional_injective
  apply Subtype.ext
  apply DFunLike.ext
  intro f
  rw [probability_functional_apply, probability_functional_apply, balanced_probability_integral]
  let c : ℝ := (f xb - f xa) / (b - a)
  let g : C(K,ℝ) := ContinuousMap.const K (f xa) + c • (lam - ContinuousMap.const K a)
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hae : (fun x => f x) =ᵐ[(ν : Measure K)] (fun x => g x) := by
    filter_upwards [hend] with x hx
    rcases hx with hx | hx
    · have he : x = xa := hinj (hx.trans hxa.symm)
      simp [g, he, hxa]
    · have he : x = xb := hinj (hx.trans hxb.symm)
      simp only [g, c, he, ContinuousMap.add_apply, ContinuousMap.const_apply,
        ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul, hxb]
      field_simp [hba]
  rw [integral_congr_ae hae]
  change (probabilityFunctional ν).1 g = _
  dsimp only [g]
  rw [map_add, _root_.map_smul, map_sub, positive_unit_const (probabilityFunctional ν).2,
    positive_unit_const (probabilityFunctional ν).2, probability_functional_apply, hmean]
  dsimp [c]
  field_simp [hba]
  ring

theorem balanced_probability_reweight (xa xb : K) (q : C(K,ℝ)) (hq : ∀ x, 0 ≤ q x)
    (hreg : 0 < ∫ x, q x ∂(balancedProbability xa xb : Measure K))
    (c : ℝ) (hc : 0 < c) (hqa : q xa = c) (hqb : q xb = c) :
    probabilityReweight (balancedProbability xa xb) q hq hreg = balancedProbability xa xb := by
  apply probability_functional_injective
  apply Subtype.ext
  apply DFunLike.ext
  intro f
  rw [probability_functional_apply, probability_reweight_integral,
    probability_functional_apply]
  simp only [balanced_probability_integral, hqa, hqb]
  field_simp [hc.ne']
  ring

def balancedProbabilityState (xa xb : K) : ProbabilityState K :=
  (balancedProbability xa xb, balancedProbability xa xb)

theorem balanced_probability_mean (lam : C(K,ℝ)) (xa xb : K) (a b : ℝ)
    (hxa : lam xa = a) (hxb : lam xb = b) :
    probabilityMean lam (balancedProbabilityState xa xb) = (a + b) / 2 := by
  change (∫ x, lam x ∂(balancedProbability xa xb : Measure K)) = _
  rw [balanced_probability_integral, hxa, hxb]

theorem balanced_probability_multiplier (lam : C(K,ℝ)) (xa xb : K) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b) :
    quadraticMultiplier lam (probabilityMean lam (balancedProbabilityState xa xb)) xa = (rate a b)^2 ∧
    quadraticMultiplier lam (probabilityMean lam (balancedProbabilityState xa xb)) xb = (rate a b)^2 := by
  rw [balanced_probability_mean lam xa xb a b hxa hxb]
  simp only [quadraticMultiplier_apply, hxa, hxb]
  have hab0 : a + b ≠ 0 := by linarith
  have hba0 : b + a ≠ 0 := by linarith
  constructor <;> dsimp [rate] <;> field_simp [hab0, hba0] <;> ring

theorem balanced_probability_growth_sq (lam : C(K,ℝ)) (xa xb : K) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b) :
    probabilityGrowthSq lam (balancedProbabilityState xa xb) = (rate a b)^2 := by
  have he := balanced_probability_multiplier lam xa xb a b ha hab hxa hxb
  simp only [quadraticMultiplier_apply] at he
  unfold probabilityGrowthSq
  change (∫ x, (1 - lam x / probabilityMean lam (balancedProbabilityState xa xb))^2
    ∂(balancedProbability xa xb : Measure K)) = _
  rw [balanced_probability_integral, he.1, he.2]
  ring

theorem balanced_probability_growth (lam : C(K,ℝ)) (xa xb : K) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b) :
    probabilityGrowth lam (balancedProbabilityState xa xb) = rate a b := by
  rw [probabilityGrowth, balanced_probability_growth_sq lam xa xb a b ha hab hxa hxb,
    Real.sqrt_sq (rate_pos ha hab).le]

theorem balanced_probability_fixed (lam : C(K,ℝ)) (xa xb : K) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b) :
    probabilityMap lam (balancedProbabilityState xa xb) = balancedProbabilityState xa xb := by
  have hg : 0 < probabilityGrowthSq lam (balancedProbabilityState xa xb) := by
    rw [balanced_probability_growth_sq lam xa xb a b ha hab hxa hxb]
    exact sq_pos_of_pos (rate_pos ha hab)
  have he := balanced_probability_multiplier lam xa xb a b ha hab hxa hxb
  rw [probabilityMap, dif_pos hg]
  apply Prod.ext
  · exact balanced_probability_reweight xa xb _ (quadraticMultiplier_nonneg _ _)
      (by simpa only [quadraticMultiplier_apply, probabilityGrowthSq, balancedProbabilityState] using hg)
      ((rate a b)^2)
      (sq_pos_of_pos (rate_pos ha hab)) he.1 he.2
  · rfl

end BB
