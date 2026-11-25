import BB.FunctionalDynamics
import BB.UniversalFinite
import BB.FunctionalSharp

/-!
# Finite spectral states embedded in compact positive functionals

A simplex vector defines the positive unit functional given by its finite
weighted evaluation sum. Mean, growth, and the total BB update commute with
this embedding, including zero-growth states. Consequently all finite prefix
products agree exactly.
-/

namespace BB
noncomputable section
open scoped BigOperators Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
variable {ι : Type*} [Fintype ι]

def simplexDual (nodes : ι → K) (w : ι → ℝ) : NormedSpace.Dual ℝ C(K, ℝ) :=
  ∑ i, w i • ContinuousMap.evalCLM ℝ (nodes i)

lemma simplex_dual_apply (nodes : ι → K) (w : ι → ℝ) (f : C(K, ℝ)) :
    simplexDual nodes w f = ∑ i, w i * f (nodes i) := by
  simp only [simplexDual, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  rfl

def simplexFunctional (nodes : ι → K) (w : Simplex ι) : PositiveState K :=
  ⟨NormedSpace.Dual.toWeakDual (simplexDual nodes w.1), by
    constructor
    · intro f hf
      change 0 ≤ simplexDual nodes w.1 f
      rw [simplex_dual_apply]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (w.2.1 i) (hf (nodes i)))
    · change simplexDual nodes w.1 1 = 1
      rw [simplex_dual_apply]
      simpa using w.2.2⟩

lemma simplex_functional_apply (nodes : ι → K) (w : Simplex ι) (f : C(K, ℝ)) :
    (simplexFunctional nodes w).1 f = ∑ i, w.1 i * f (nodes i) :=
  simplex_dual_apply nodes w.1 f

lemma simplex_functional_continuous (nodes : ι → K) :
    Continuous (simplexFunctional nodes) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro f
  change Continuous (fun w : Simplex ι => (simplexFunctional nodes w).1 f)
  simp only [simplex_functional_apply]
  apply continuous_finset_sum
  intro i _
  exact ((continuous_apply i).comp continuous_subtype_val).mul continuous_const

def finiteFunctionalEmbedding (nodes : ι → K) (χ : SpectralState ι) : FunctionalState K :=
  (simplexFunctional nodes χ.1, simplexFunctional nodes χ.2)

lemma finite_functional_embedding_continuous (nodes : ι → K) :
    Continuous (finiteFunctionalEmbedding nodes) :=
  ((simplex_functional_continuous nodes).comp continuous_fst).prod_mk
    ((simplex_functional_continuous nodes).comp continuous_snd)

lemma functional_mean_embedding (lam : C(K, ℝ)) (nodes : ι → K) (χ : SpectralState ι) :
    functionalMean lam (finiteFunctionalEmbedding nodes χ) =
      mean (fun i => lam (nodes i)) χ.2.1 := by
  change (simplexFunctional nodes χ.2).1 lam = _
  rw [simplex_functional_apply]
  unfold mean
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma functional_growth_sq_embedding (lam : C(K, ℝ)) (nodes : ι → K) (χ : SpectralState ι) :
    functionalGrowthSq lam (finiteFunctionalEmbedding nodes χ) =
      stateGrowthSq (fun i => lam (nodes i)) χ := by
  unfold functionalGrowthSq
  rw [functional_mean_embedding]
  change (simplexFunctional nodes χ.1).1 _ = _
  rw [simplex_functional_apply]
  unfold stateGrowthSq growthSq multiplier
  apply Finset.sum_congr rfl
  intro i _
  rw [quadraticMultiplier_apply]
  ring

lemma functional_growth_embedding (lam : C(K, ℝ)) (nodes : ι → K) (χ : SpectralState ι) :
    functionalGrowth lam (finiteFunctionalEmbedding nodes χ) =
      stateGrowth (fun i => lam (nodes i)) χ := by
  unfold functionalGrowth stateGrowth
  rw [functional_growth_sq_embedding]

lemma functional_map_embedding (lam : C(K, ℝ)) (nodes : ι → K) (χ : SpectralState ι) :
    finiteFunctionalEmbedding nodes (spectralMap (fun i => lam (nodes i)) χ) =
      functionalMap lam (finiteFunctionalEmbedding nodes χ) := by
  by_cases hR : 0 < stateGrowthSq (fun i => lam (nodes i)) χ
  · have hFR : 0 < functionalGrowthSq lam (finiteFunctionalEmbedding nodes χ) := by
      rw [functional_growth_sq_embedding]
      exact hR
    apply Prod.ext
    · apply Subtype.ext
      apply DFunLike.ext
      intro f
      change (simplexFunctional nodes (spectralMap (fun i => lam (nodes i)) χ).1).1 f =
        (functionalMap lam (finiteFunctionalEmbedding nodes χ)).1.1 f
      rw [functional_map_regular_test lam f _ hFR, functional_growth_sq_embedding,
        functional_mean_embedding, simplex_functional_apply]
      change (∑ i, ((spectralMap (fun i => lam (nodes i)) χ).1.1 i) * f (nodes i)) =
        (simplexFunctional nodes χ.1).1 (quadraticMultiplier lam (mean (fun i => lam (nodes i)) χ.2.1) * f) /
          stateGrowthSq (fun i => lam (nodes i)) χ
      rw [simplex_functional_apply, (spectral_map_regular _ χ hR).1, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      simp only [weightUpdate, ContinuousMap.mul_apply, quadraticMultiplier_apply,
        multiplier, stateGrowthSq]
      ring
    · exact congrArg (simplexFunctional nodes) (spectral_map_regular _ χ hR).2 |>.trans
        (functional_map_regular lam _ hFR).2.symm
  · have hFR : ¬0 < functionalGrowthSq lam (finiteFunctionalEmbedding nodes χ) := by
      simpa only [functional_growth_sq_embedding] using hR
    simp only [spectralMap, dif_neg hR, functionalMap, dif_neg hFR]

lemma functional_iterate_embedding (lam : C(K, ℝ)) (nodes : ι → K) (n : ℕ) (χ : SpectralState ι) :
    finiteFunctionalEmbedding nodes ((spectralMap (fun i => lam (nodes i)))^[n] χ) =
      (functionalMap lam)^[n] (finiteFunctionalEmbedding nodes χ) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', functional_map_embedding, ih, Function.iterate_succ_apply']

lemma functional_prefix_embedding (lam : C(K, ℝ)) (nodes : ι → K) (n : ℕ) (χ : SpectralState ι) :
    prefixProduct (functionalGrowth lam) (functionalMap lam) n (finiteFunctionalEmbedding nodes χ) =
      prefixProduct (stateGrowth (fun i => lam (nodes i))) (spectralMap (fun i => lam (nodes i))) n χ := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
    rw [prefix_product_succ, prefix_product_succ, functional_growth_embedding,
      ← functional_map_embedding, ih]


/-- A single compact functional-state bound supplies the same finite-state
constant in every dimension and for every spectrum in the interval. -/
lemma uniform_spectral_envelope_exists (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hγ : rate A B < γ) :
    ∃ C : ℝ, 0 < C ∧ UniformSpectralEnvelope A B γ C := by
  obtain ⟨C, hC, henv⟩ := interval_functional_envelope A B γ hA hAB hγ
  refine ⟨C, hC, ?_⟩
  intro d lam hlam n χ
  let nodes : Fin d → Set.Icc A B := fun i => ⟨lam i, hlam i⟩
  have hbound := henv n (finiteFunctionalEmbedding nodes χ)
  rw [functional_prefix_embedding] at hbound
  exact hbound

end
end BB
