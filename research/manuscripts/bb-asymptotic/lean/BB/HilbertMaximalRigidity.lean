import BB.HilbertMaximalMidpoint

/-!
# Endpoint concentration of a maximal probability-state law

Midpoint equality and integral equality force the actual first spectral
measure onto the two endpoint level sets. This uses actual Bochner integral
rigidity; no finite-support hypothesis is assumed.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

lemma midpoint_quadratic_multiplier (lam : C(K,ℝ)) (a b : ℝ) (x : K) :
    quadraticMultiplier lam ((a+b)/2) x = (1-2*lam x/(a+b))^2 := by
  rw [quadraticMultiplier_apply,div_div_eq_mul_div]
  congr 2
  ring

lemma probability_midpoint_growth_sq_le (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (hmean : probabilityMean lam χ = (a+b)/2) : probabilityGrowthSq lam χ ≤ (rate a b)^2 := by
  let q := quadraticMultiplier lam ((a+b)/2)
  have hq : ∀ x, q x ≤ (rate a b)^2 := by
    intro x
    rw [midpoint_quadratic_multiplier]
    simpa only [rate,add_comm] using midpoint_multiplier_le a b (lam x) ha hab (hlam x).1 (hlam x).2
  have hi := integral_mono (continuous_integrable_probability χ.1 q) (integrable_const ((rate a b)^2)) hq
  simp only [integral_const,measure_univ,ENNReal.one_toReal,one_smul] at hi
  simpa only [probabilityGrowthSq,hmean,q,quadraticMultiplier_apply] using hi

lemma probability_midpoint_growth_le (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (hmean : probabilityMean lam χ = (a+b)/2) : probabilityGrowth lam χ ≤ rate a b :=
  (Real.sqrt_le_left (rate_pos ha hab).le).mpr
    (probability_midpoint_growth_sq_le lam χ a b ha hab hlam hmean)

lemma probability_midpoint_integral_rigidity (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (hmean : probabilityMean lam χ = (a+b)/2)
    (hR : probabilityGrowthSq lam χ = (rate a b)^2) :
    ∀ᵐ x ∂(χ.1 : Measure K), lam x = a ∨ lam x = b := by
  let q := quadraticMultiplier lam ((a+b)/2)
  have hq : ∀ x, q x ≤ (rate a b)^2 := by
    intro x
    rw [midpoint_quadratic_multiplier]
    simpa only [rate,add_comm] using midpoint_multiplier_le a b (lam x) ha hab (hlam x).1 (hlam x).2
  have heq : (∫ x, q x ∂(χ.1 : Measure K)) = ∫ _x : K, (rate a b)^2 ∂(χ.1 : Measure K) := by
    simpa only [probabilityGrowthSq,hmean,q,quadraticMultiplier_apply,integral_const,
      measure_univ,ENNReal.one_toReal,one_smul] using hR
  have hae := (integral_eq_iff_of_ae_le (continuous_integrable_probability χ.1 q)
    (integrable_const ((rate a b)^2)) (eventually_of_forall hq)).mp heq
  filter_upwards [hae] with x hx
  apply (midpoint_multiplier_eq_iff a b (lam x) ha hab).mp
  simpa only [q,midpoint_quadratic_multiplier,rate,add_comm] using hx

section Invariant
variable [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

/-- All equality information required to identify the balanced endpoint
probability measure. The law need not be ergodic. -/
theorem probability_maximal_rigidity (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    ∀ᵐ χ ∂μ, probabilityMean lam χ = (a+b)/2 ∧
      (∫ x, lam x ∂(χ.1 : Measure K)) = (a+b)/2 ∧
      probabilityGrowth lam χ = rate a b ∧
      (∀ᵐ x ∂(χ.1 : Measure K), lam x = a ∨ lam x = b) := by
  have hmean := probability_maximal_midpoint lam a b ha hab hlam μ hT hregular hf hmaximal
  have hmeanT := hT.quasiMeasurePreserving.ae hmean
  have hle : ∀ᵐ χ ∂μ, probabilityGrowth lam χ ≤ rate a b :=
    hmean.mono (fun χ hχ => probability_midpoint_growth_le lam χ a b ha hab hlam hχ)
  have hroot := log_integral_rigidity μ (probabilityGrowth lam) (rate a b) (rate_pos ha hab)
    hregular hle hf hmaximal
  filter_upwards [hmean,hmeanT,hregular,hroot] with χ hm hmT hr hroot
  have hRpos : 0 < probabilityGrowthSq lam χ := Real.sqrt_pos.mp hr
  have hshift : (probabilityMap lam χ).2 = χ.1 := by rw [probabilityMap,dif_pos hRpos]
  have hfirst : (∫ x, lam x ∂(χ.1 : Measure K)) = (a+b)/2 := by
    change (∫ x, lam x ∂((probabilityMap lam χ).2 : Measure K)) = _ at hmT
    rwa [hshift] at hmT
  have hR : probabilityGrowthSq lam χ = (rate a b)^2 := by
    calc
      probabilityGrowthSq lam χ = probabilityGrowth lam χ ^ 2 :=
        (Real.sq_sqrt (probability_growth_sq_nonneg lam χ)).symm
      _ = (rate a b)^2 := by rw [hroot]
  exact ⟨hm,hfirst,hroot,probability_midpoint_integral_rigidity lam χ a b ha hab hlam hm hR⟩

end Invariant
end BB
