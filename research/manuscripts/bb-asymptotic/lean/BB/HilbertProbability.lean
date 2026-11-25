import BB.Hilbert
import BB.FunctionalSharp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Actual probability-measure states and the functional compact model

Probability measures are embedded by their actual Bochner integrals. The
normalized measure update is constructed with `withDensity`; all mean, growth,
and update identities are proved. Weak continuity is the library's weak
probability-measure topology, rather than an artificially chosen topology.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K]

lemma continuous_integrable_probability (ν : ProbabilityMeasure K) (f : C(K,ℝ)) :
    Integrable f (ν : Measure K) :=
  (BoundedContinuousFunction.mkOfCompact f).integrable (ν : Measure K)

def probabilityIntegralLinear (ν : ProbabilityMeasure K) : C(K,ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂(ν : Measure K)
  map_add' f g := integral_add (continuous_integrable_probability ν f) (continuous_integrable_probability ν g)
  map_smul' c f := integral_smul c f

def probabilityIntegralDual (ν : ProbabilityMeasure K) : NormedSpace.Dual ℝ C(K,ℝ) :=
  (probabilityIntegralLinear ν).mkContinuous 1 (by
    intro f
    have hb := norm_integral_le_of_norm_le_const (μ := (ν : Measure K))
      (Filter.eventually_of_forall (fun x => f.norm_coe_le_norm x))
    simpa only [probabilityIntegralLinear, LinearMap.coe_mk, AddHom.coe_mk,
      measure_univ, ENNReal.one_toReal, mul_one, one_mul] using hb)

def probabilityFunctional (ν : ProbabilityMeasure K) : PositiveState K :=
  ⟨NormedSpace.Dual.toWeakDual (probabilityIntegralDual ν), by
    constructor
    · intro f hf
      exact integral_nonneg hf
    · change (∫ _x : K, (1:ℝ) ∂(ν : Measure K)) = 1
      simp⟩

@[simp] lemma probability_functional_apply (ν : ProbabilityMeasure K) (f : C(K,ℝ)) :
    (probabilityFunctional ν).1 f = ∫ x, f x ∂(ν : Measure K) := rfl

lemma probability_functional_continuous : Continuous (probabilityFunctional : ProbabilityMeasure K → PositiveState K) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro f
  apply continuous_iff_continuousAt.mpr
  intro ν
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp tendsto_id)
    (BoundedContinuousFunction.mkOfCompact f)

lemma probability_functional_tendsto_iff {J : Type*} {l : Filter J}
    (νs : J → ProbabilityMeasure K) (ν : ProbabilityMeasure K) :
    Tendsto (fun j => probabilityFunctional (νs j)) l (𝓝 (probabilityFunctional ν)) ↔
      Tendsto νs l (𝓝 ν) := by
  constructor
  · intro h
    apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    exact (positive_state_eval_continuous f.toContinuousMap).continuousAt.tendsto.comp h
  · intro h
    exact probability_functional_continuous.continuousAt.tendsto.comp h

lemma probability_functional_injective [HasOuterApproxClosed K] [BorelSpace K] :
    Function.Injective (probabilityFunctional : ProbabilityMeasure K → PositiveState K) := by
  intro μ ν heq
  have h : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) :=
    (probability_functional_tendsto_iff (fun _ : ℕ => μ) ν).mp (by rw [heq]; exact tendsto_const_nhds)
  exact tendsto_nhds_unique tendsto_const_nhds h

lemma continuous_density_mass (ν : ProbabilityMeasure K) (q : C(K,ℝ)) (hq : ∀ x, 0 ≤ q x) :
    (∫⁻ x, ENNReal.ofReal (q x) ∂(ν : Measure K)) =
      ENNReal.ofReal (∫ x, q x ∂(ν : Measure K)) :=
  (ofReal_integral_eq_lintegral_ofReal (continuous_integrable_probability ν q)
    (Filter.eventually_of_forall hq)).symm

def probabilityReweight (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (hreg : 0 < ∫ x, q x ∂(ν : Measure K)) : ProbabilityMeasure K :=
  ⟨normalizedReweight (ν : Measure K) (fun x => ENNReal.ofReal (q x)), by
    apply normalizedReweight_probability
    · rw [continuous_density_mass ν q hq]
      exact (ENNReal.ofReal_pos.mpr hreg).ne'
    · rw [continuous_density_mass ν q hq]
      exact ENNReal.ofReal_ne_top⟩

lemma probability_reweight_integral (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (hreg : 0 < ∫ x, q x ∂(ν : Measure K)) (f : C(K,ℝ)) :
    (∫ x, f x ∂(probabilityReweight ν q hq hreg : Measure K)) =
      (∫ x, q x*f x ∂(ν : Measure K)) / (∫ x, q x ∂(ν : Measure K)) := by
  change (∫ x, f x ∂normalizedReweight (ν : Measure K) (fun x => ENNReal.ofReal (q x))) = _
  rw [normalizedReweight, integral_smul_measure, continuous_density_mass ν q hq,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hreg.le]
  let qNN : K → ℝ≥0 := fun x => ⟨q x,hq x⟩
  have hden : (fun x : K => ENNReal.ofReal (q x)) = (fun x => (qNN x : ℝ≥0∞)) := by
    funext x
    exact ENNReal.ofReal_eq_coe_nnreal (hq x)
  have hqNN : Measurable qNN := measurable_coe_nnreal_real_iff.mp q.continuous.measurable
  rw [hden, integral_withDensity_eq_integral_smul hqNN]
  change (∫ x, q x ∂(ν : Measure K))⁻¹ * (∫ x, q x*f x ∂(ν : Measure K)) = _
  ring

lemma probability_reweight_functional (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (hreg : 0 < ∫ x, q x ∂(ν : Measure K)) :
    probabilityFunctional (probabilityReweight ν q hq hreg) =
      positiveReweight (probabilityFunctional ν) q hq hreg := by
  apply Subtype.ext
  apply DFunLike.ext
  intro f
  rw [positiveReweight_apply, probability_functional_apply, probability_reweight_integral]
  rfl

abbrev ProbabilityState (K : Type*) [MeasurableSpace K] := ProbabilityMeasure K × ProbabilityMeasure K

def probabilityStateEmbedding (χ : ProbabilityState K) : FunctionalState K :=
  (probabilityFunctional χ.1, probabilityFunctional χ.2)

def probabilityMean (lam : C(K,ℝ)) (χ : ProbabilityState K) : ℝ := ∫ x, lam x ∂(χ.2 : Measure K)

def probabilityGrowthSq (lam : C(K,ℝ)) (χ : ProbabilityState K) : ℝ :=
  ∫ x, (1-lam x/probabilityMean lam χ)^2 ∂(χ.1 : Measure K)

def probabilityGrowth (lam : C(K,ℝ)) (χ : ProbabilityState K) : ℝ := Real.sqrt (probabilityGrowthSq lam χ)

def probabilityMap (lam : C(K,ℝ)) (χ : ProbabilityState K) : ProbabilityState K :=
  if h : 0 < probabilityGrowthSq lam χ then
    (probabilityReweight χ.1 (quadraticMultiplier lam (probabilityMean lam χ))
      (quadraticMultiplier_nonneg lam (probabilityMean lam χ))
      (by simpa only [quadraticMultiplier_apply,probabilityGrowthSq] using h), χ.1)
  else χ

@[simp] lemma probability_mean_embedding (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    functionalMean lam (probabilityStateEmbedding χ) = probabilityMean lam χ := rfl

@[simp] lemma probability_growth_sq_embedding (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    functionalGrowthSq lam (probabilityStateEmbedding χ) = probabilityGrowthSq lam χ := by
  change (∫ x, quadraticMultiplier lam (probabilityMean lam χ) x ∂(χ.1 : Measure K)) = _
  simp only [quadraticMultiplier_apply, probabilityGrowthSq]

@[simp] lemma probability_growth_embedding (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    functionalGrowth lam (probabilityStateEmbedding χ) = probabilityGrowth lam χ := by
  unfold functionalGrowth probabilityGrowth
  rw [probability_growth_sq_embedding]

lemma probability_map_embedding (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    probabilityStateEmbedding (probabilityMap lam χ) = functionalMap lam (probabilityStateEmbedding χ) := by
  by_cases h : 0 < probabilityGrowthSq lam χ
  · have hf : 0 < functionalGrowthSq lam (probabilityStateEmbedding χ) := by rwa [probability_growth_sq_embedding]
    rw [probabilityMap,dif_pos h,functionalMap,dif_pos hf]
    change (probabilityFunctional _,probabilityFunctional χ.1) = _
    rw [probability_reweight_functional]
    rfl
  · have hf : ¬0 < functionalGrowthSq lam (probabilityStateEmbedding χ) := by rwa [probability_growth_sq_embedding]
    simp only [probabilityMap, dif_neg h, functionalMap, dif_neg hf]

lemma probability_state_embedding_continuous : Continuous (probabilityStateEmbedding : ProbabilityState K → FunctionalState K) :=
  (probability_functional_continuous.comp continuous_fst).prod_mk
    (probability_functional_continuous.comp continuous_snd)

lemma probability_state_embedding_tendsto_iff {J : Type*} {l : Filter J}
    (χs : J → ProbabilityState K) (χ : ProbabilityState K) :
    Tendsto (fun j => probabilityStateEmbedding (χs j)) l (𝓝 (probabilityStateEmbedding χ)) ↔
      Tendsto χs l (𝓝 χ) := by
  constructor
  · intro h
    exact ((probability_functional_tendsto_iff _ _).mp (continuous_fst.continuousAt.tendsto.comp h)).prod_mk_nhds
      ((probability_functional_tendsto_iff _ _).mp (continuous_snd.continuousAt.tendsto.comp h))
  · intro h
    exact probability_state_embedding_continuous.continuousAt.tendsto.comp h

lemma probability_growth_sq_nonneg (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    0 ≤ probabilityGrowthSq lam χ := by
  rw [← probability_growth_sq_embedding]
  exact functional_growth_sq_nonneg _ _

lemma probability_growth_nonneg (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    0 ≤ probabilityGrowth lam χ := Real.sqrt_nonneg _

lemma probability_growth_sq_continuous (lam : C(K,ℝ)) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ x, a ≤ lam x) : Continuous (probabilityGrowthSq lam) := by
  have h := (functional_growth_sq_continuous lam a ha hlam).comp probability_state_embedding_continuous
  simpa only [Function.comp_def, probability_growth_sq_embedding] using h

lemma probability_growth_continuous (lam : C(K,ℝ)) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ x, a ≤ lam x) : Continuous (probabilityGrowth lam) :=
  (probability_growth_sq_continuous lam a ha hlam).sqrt

lemma probability_map_continuousAt_regular (lam : C(K,ℝ)) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ x, a ≤ lam x) (χ : ProbabilityState K) (hreg : probabilityGrowth lam χ ≠ 0) :
    ContinuousAt (probabilityMap lam) χ := by
  apply (probability_state_embedding_tendsto_iff (probabilityMap lam) _).mp
  have hF : functionalGrowth lam (probabilityStateEmbedding χ) ≠ 0 := by rwa [probability_growth_embedding]
  have h := (functional_map_continuousAt_regular lam a ha hlam _ hF).tendsto.comp
    probability_state_embedding_continuous.continuousAt.tendsto
  simpa only [probability_map_embedding] using h

lemma probability_prefix_embedding (lam : C(K,ℝ)) (n : ℕ) (χ : ProbabilityState K) :
    prefixProduct (functionalGrowth lam) (functionalMap lam) n (probabilityStateEmbedding χ) =
      prefixProduct (probabilityGrowth lam) (probabilityMap lam) n χ := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih => rw [prefix_product_succ, prefix_product_succ, probability_growth_embedding,
      ← probability_map_embedding, ih]

end BB
