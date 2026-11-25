import BB.PositiveState
import BB.Cocycle

/-!
# BB dynamics on compact positive functional states

The topology is the proved weak-star compact topology.  The normalized update
is constructed from positive reweighting.  Every finite multiplier product is
continuous, including at zero multipliers under the chosen total continuation.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace BB

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

abbrev FunctionalState (K : Type*) [TopologicalSpace K] [CompactSpace K] :=
  PositiveState K × PositiveState K

def functionalMean (lam : C(K, ℝ)) (χ : FunctionalState K) : ℝ := χ.2.1 lam

def functionalGrowthSq (lam : C(K, ℝ)) (χ : FunctionalState K) : ℝ :=
  χ.1.1 (quadraticMultiplier lam (functionalMean lam χ))

def functionalGrowth (lam : C(K, ℝ)) (χ : FunctionalState K) : ℝ :=
  Real.sqrt (functionalGrowthSq lam χ)

def functionalMap (lam : C(K, ℝ)) (χ : FunctionalState K) : FunctionalState K :=
  if h : 0 < functionalGrowthSq lam χ then
    (positiveReweight χ.1 (quadraticMultiplier lam (functionalMean lam χ))
      (quadraticMultiplier_nonneg lam _) h, χ.1)
  else χ

theorem functional_mean_continuous (lam : C(K, ℝ)) : Continuous (functionalMean lam) :=
  (positive_state_eval_continuous lam).comp continuous_snd

theorem functional_mean_lower (lam : C(K, ℝ)) (a : ℝ) (hlam : ∀ x, a ≤ lam x)
    (χ : FunctionalState K) : a ≤ functionalMean lam χ :=
  positive_unit_lower_bound χ.2 lam a hlam

theorem functional_mean_upper (lam : C(K, ℝ)) (b : ℝ) (hlam : ∀ x, lam x ≤ b)
    (χ : FunctionalState K) : functionalMean lam χ ≤ b :=
  positive_unit_upper_bound χ.2 lam b hlam

theorem functional_growth_sq_nonneg (lam : C(K, ℝ)) (χ : FunctionalState K) :
    0 ≤ functionalGrowthSq lam χ :=
  χ.1.2.1 _ (quadraticMultiplier_nonneg lam _)

theorem functional_growth_nonneg (lam : C(K, ℝ)) (χ : FunctionalState K) :
    0 ≤ functionalGrowth lam χ := Real.sqrt_nonneg _

theorem functional_growth_sq_identity (lam : C(K, ℝ)) (χ : FunctionalState K) :
    functionalGrowth lam χ ^ 2 = functionalGrowthSq lam χ :=
  Real.sq_sqrt (functional_growth_sq_nonneg lam χ)

theorem functional_growth_moments (lam : C(K, ℝ)) (χ : FunctionalState K) :
    functionalGrowthSq lam χ = 1 - (2 * (functionalMean lam χ)⁻¹) * χ.1.1 lam +
      ((functionalMean lam χ)⁻¹)^2 * χ.1.1 (lam^2) := by
  simpa only [mul_one, χ.1.2.2] using
    quadratic_test_identity χ.1 lam 1 (functionalMean lam χ)

theorem functional_numerator_continuous (lam f : C(K, ℝ)) (a : ℝ)
    (ha : 0 < a) (hlam : ∀ x, a ≤ lam x) :
    Continuous (fun χ : FunctionalState K =>
      χ.1.1 (quadraticMultiplier lam (functionalMean lam χ) * f)) := by
  have hu : Continuous (fun χ : FunctionalState K => (functionalMean lam χ)⁻¹) :=
    (functional_mean_continuous lam).inv₀
      (fun χ => ne_of_gt (ha.trans_le (functional_mean_lower lam a hlam χ)))
  have hf : Continuous (fun χ : FunctionalState K => χ.1.1 f) :=
    (positive_state_eval_continuous f).comp continuous_fst
  have hlf : Continuous (fun χ : FunctionalState K => χ.1.1 (lam * f)) :=
    (positive_state_eval_continuous (lam * f)).comp continuous_fst
  have hllf : Continuous (fun χ : FunctionalState K => χ.1.1 (lam^2 * f)) :=
    (positive_state_eval_continuous (lam^2 * f)).comp continuous_fst
  have hcont := (hf.sub (((continuous_const : Continuous (fun _ : FunctionalState K => (2 : ℝ))).mul hu).mul hlf)).add ((hu.pow 2).mul hllf)
  simpa only [quadratic_test_identity] using hcont

theorem functional_growth_sq_continuous (lam : C(K, ℝ)) (a : ℝ)
    (ha : 0 < a) (hlam : ∀ x, a ≤ lam x) : Continuous (functionalGrowthSq lam) := by
  simpa only [mul_one] using functional_numerator_continuous lam 1 a ha hlam

theorem functional_growth_continuous (lam : C(K, ℝ)) (a : ℝ)
    (ha : 0 < a) (hlam : ∀ x, a ≤ lam x) : Continuous (functionalGrowth lam) :=
  (functional_growth_sq_continuous lam a ha hlam).sqrt

theorem functional_map_regular (lam : C(K, ℝ)) (χ : FunctionalState K)
    (hR : 0 < functionalGrowthSq lam χ) :
    (functionalMap lam χ).1 =
      positiveReweight χ.1 (quadraticMultiplier lam (functionalMean lam χ))
        (quadraticMultiplier_nonneg lam _) hR ∧
      (functionalMap lam χ).2 = χ.1 := by
  simp only [functionalMap, dif_pos hR]
  exact ⟨trivial, trivial⟩

theorem functional_map_regular_test (lam f : C(K, ℝ)) (χ : FunctionalState K)
    (hR : 0 < functionalGrowthSq lam χ) :
    (functionalMap lam χ).1.1 f =
      χ.1.1 (quadraticMultiplier lam (functionalMean lam χ) * f) / functionalGrowthSq lam χ := by
  rw [(functional_map_regular lam χ hR).1, positiveReweight_apply]
  rfl

theorem functional_map_continuousAt_regular (lam : C(K, ℝ)) (a : ℝ)
    (ha : 0 < a) (hlam : ∀ x, a ≤ lam x) (χ : FunctionalState K)
    (hχ : functionalGrowth lam χ ≠ 0) : ContinuousAt (functionalMap lam) χ := by
  have hR : 0 < functionalGrowthSq lam χ :=
    lt_of_le_of_ne (functional_growth_sq_nonneg lam χ)
      (fun hz => hχ (by simp [functionalGrowth, hz.symm]))
  have hRcont := functional_growth_sq_continuous lam a ha hlam
  have hreg : ∀ᶠ y in 𝓝 χ, 0 < functionalGrowthSq lam y :=
    (isOpen_lt continuous_const hRcont).mem_nhds hR
  have hfirst : ContinuousAt (fun y => (functionalMap lam y).1) χ := by
    change Tendsto _ (𝓝 χ) (𝓝 _)
    rw [tendsto_subtype_rng, tendsto_iff_forall_eval_tendsto_topDualPairing]
    intro f
    change Tendsto (fun y => (functionalMap lam y).1.1 f) (𝓝 χ)
      (𝓝 ((functionalMap lam χ).1.1 f))
    have he : (fun y => (functionalMap lam y).1.1 f) =ᶠ[𝓝 χ]
        (fun y => y.1.1 (quadraticMultiplier lam (functionalMean lam y) * f) /
          functionalGrowthSq lam y) := by
      filter_upwards [hreg] with y hy
      exact functional_map_regular_test lam f y hy
    rw [functional_map_regular_test lam f χ hR]
    exact (tendsto_congr' he).mpr
      ((functional_numerator_continuous lam f a ha hlam).continuousAt.div
        hRcont.continuousAt (ne_of_gt hR))
  have hsecond : ContinuousAt (fun y => (functionalMap lam y).2) χ := by
    have he : (fun y => (functionalMap lam y).2) =ᶠ[𝓝 χ] (fun y => y.1) := by
      filter_upwards [hreg] with y hy
      exact (functional_map_regular lam y hy).2
    change Tendsto _ (𝓝 χ) (𝓝 ((functionalMap lam χ).2))
    rw [(functional_map_regular lam χ hR).2]
    exact (tendsto_congr' he).mpr continuous_fst.continuousAt
  exact hfirst.prod hsecond

theorem functional_growth_bound (lam : C(K, ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (χ : FunctionalState K) : functionalGrowth lam χ ≤ 1 + b/a := by
  let u := functionalMean lam χ
  have hua : a ≤ u := functional_mean_lower lam a (fun x => (hlam x).1) χ
  have hu : 0 < u := ha.trans_le hua
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 ≤ 1 + b/a := by positivity
  have hpoint : ∀ x, quadraticMultiplier lam u x ≤ (1+b/a)^2 := by
    intro x
    have hnum : 0 ≤ lam x := ha.le.trans (hlam x).1
    have hr0 : 0 ≤ lam x/u := div_nonneg hnum hu.le
    have hr : lam x/u ≤ b/a := by
      apply (div_le_div_iff hu ha).mpr
      exact (mul_le_mul_of_nonneg_right (hlam x).2 ha.le).trans
        (mul_le_mul_of_nonneg_left hua hb.le)
    have hq : |1 - lam x/u| ≤ 1 + b/a := by
      apply abs_le.mpr
      constructor <;> linarith
    rw [quadraticMultiplier_apply]
    exact (sq_abs (1-lam x/u)).symm.le.trans
      (pow_le_pow_left (abs_nonneg _) hq 2)
  have hsum : functionalGrowthSq lam χ ≤ (1+b/a)^2 :=
    positive_unit_upper_bound χ.1 (quadraticMultiplier lam u) _ hpoint
  calc
    functionalGrowth lam χ ≤ Real.sqrt ((1+b/a)^2) := Real.sqrt_le_sqrt hsum
    _ = 1+b/a := Real.sqrt_sq hC

theorem functional_prefix_continuous (lam : C(K, ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b) :
    ∀ n, Continuous (prefixProduct (functionalGrowth lam) (functionalMap lam) n) := by
  apply prefix_product_continuous (functionalGrowth lam) (functionalMap lam) (1+b/a)
    (by have hb := ha.trans_le hab; positivity)
    (functional_growth_nonneg lam) (functional_growth_bound lam a b ha hab hlam)
    (functional_growth_continuous lam a ha (fun x => (hlam x).1))
  exact functional_map_continuousAt_regular lam a ha (fun x => (hlam x).1)

end BB
