import BB.HilbertRestrictedWeak
import BB.HilbertPersistentSupport

/-!
# Naturality and closed-support restriction of probability dynamics

All transports below use actual pushforwards and the actual normalized
`withDensity` measure. They include the zero-growth branch of the total map.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology

variable {K L : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [MetricSpace L] [CompactSpace L] [MeasurableSpace L] [BorelSpace L]

def probabilityPush (F : C(K,L)) (ν : ProbabilityMeasure K) : ProbabilityMeasure L :=
  ν.map F.continuous.measurable.aemeasurable

lemma probability_push_integral (F : C(K,L)) (ν : ProbabilityMeasure K) (f : C(L,ℝ)) :
    (∫ y, f y ∂(probabilityPush F ν : Measure L)) = ∫ x, f (F x) ∂(ν : Measure K) := by
  exact integral_map F.continuous.measurable.aemeasurable f.continuous.measurable.aestronglyMeasurable

lemma probability_reweight_push (F : C(K,L)) (ν : ProbabilityMeasure K) (q : C(L,ℝ))
    (hq : ∀ y, 0 ≤ q y) (hreg : 0 < ∫ y, q y ∂(probabilityPush F ν : Measure L)) :
    probabilityReweight (probabilityPush F ν) q hq hreg =
      probabilityPush F (probabilityReweight ν (q.comp F) (fun x => hq (F x))
        (by simpa only [probability_push_integral] using hreg)) := by
  apply probability_functional_injective
  apply Subtype.ext
  apply DFunLike.ext
  intro f
  simp only [probability_functional_apply,probability_reweight_integral,probability_push_integral]
  change (∫ y, (q*f) y ∂(probabilityPush F ν : Measure L)) / (∫ x, q (F x) ∂(ν : Measure K)) =
    ∫ x, (f.comp F) x ∂(probabilityReweight ν (q.comp F) (fun x => hq (F x))
      (by simpa only [probability_push_integral] using hreg) : Measure K)
  rw [probability_push_integral]
  rw [probability_reweight_integral]
  rfl

def probabilityStatePush (F : C(K,L)) (χ : ProbabilityState K) : ProbabilityState L :=
  (probabilityPush F χ.1,probabilityPush F χ.2)

lemma probability_mean_push (F : C(K,L)) (lam : C(L,ℝ)) (χ : ProbabilityState K) :
    probabilityMean lam (probabilityStatePush F χ) = probabilityMean (lam.comp F) χ := by
  exact probability_push_integral F χ.2 lam

lemma probability_growth_sq_push (F : C(K,L)) (lam : C(L,ℝ)) (χ : ProbabilityState K) :
    probabilityGrowthSq lam (probabilityStatePush F χ) = probabilityGrowthSq (lam.comp F) χ := by
  simp only [probabilityGrowthSq,probability_mean_push]
  simpa only [quadraticMultiplier_apply,probabilityStatePush,ContinuousMap.comp_apply] using
    probability_push_integral F χ.1 (quadraticMultiplier lam (probabilityMean (lam.comp F) χ))

lemma probability_growth_push (F : C(K,L)) (lam : C(L,ℝ)) (χ : ProbabilityState K) :
    probabilityGrowth lam (probabilityStatePush F χ) = probabilityGrowth (lam.comp F) χ := by
  simp only [probabilityGrowth,probability_growth_sq_push]

lemma probability_map_push (F : C(K,L)) (lam : C(L,ℝ)) (χ : ProbabilityState K) :
    probabilityMap lam (probabilityStatePush F χ) =
      probabilityStatePush F (probabilityMap (lam.comp F) χ) := by
  by_cases h : 0 < probabilityGrowthSq (lam.comp F) χ
  · have h' : 0 < probabilityGrowthSq lam (probabilityStatePush F χ) := by
      rwa [probability_growth_sq_push]
    rw [probabilityMap,dif_pos h',probabilityMap,dif_pos h]
    apply Prod.ext
    · dsimp only [probabilityStatePush]
      rw [probability_reweight_push]
      congr 1
      congr 1
      · ext x
        simp only [ContinuousMap.comp_apply,quadraticMultiplier_apply,probabilityMean,
          probability_push_integral]
    · rfl
  · have h' : ¬0 < probabilityGrowthSq lam (probabilityStatePush F χ) := by
      rwa [probability_growth_sq_push]
    simp only [probabilityMap,dif_neg h,dif_neg h']

section Closed
variable (S : Set K) (hS : IsClosed S) [CompactSpace S]

def probabilityStateOnClosed (χ : ProbabilityState K)
    (hfull : (∀ᵐ x ∂(χ.1 : Measure K), x ∈ S) ∧ (∀ᵐ x ∂(χ.2 : Measure K), x ∈ S)) :
    ProbabilityState S :=
  (probabilityOnClosed χ.1 S hS hfull.1,probabilityOnClosed χ.2 S hS hfull.2)

def closedInclusion : C(S,K) := ⟨Subtype.val,continuous_subtype_val⟩

lemma probability_state_on_closed_push (χ : ProbabilityState K)
    (hfull : (∀ᵐ x ∂(χ.1 : Measure K), x ∈ S) ∧ (∀ᵐ x ∂(χ.2 : Measure K), x ∈ S)) :
    probabilityStatePush (closedInclusion S) (probabilityStateOnClosed S hS χ hfull) = χ := by
  exact Prod.ext (probability_on_closed_map χ.1 S hS hfull.1)
    (probability_on_closed_map χ.2 S hS hfull.2)

lemma probability_growth_on_closed (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (hfull : (∀ᵐ x ∂(χ.1 : Measure K), x ∈ S) ∧ (∀ᵐ x ∂(χ.2 : Measure K), x ∈ S)) :
    probabilityGrowth (lam.comp (closedInclusion S)) (probabilityStateOnClosed S hS χ hfull) =
      probabilityGrowth lam χ := by
  rw [← probability_growth_push,probability_state_on_closed_push]

lemma probability_map_on_closed_push (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (hfull : (∀ᵐ x ∂(χ.1 : Measure K), x ∈ S) ∧ (∀ᵐ x ∂(χ.2 : Measure K), x ∈ S)) :
    probabilityStatePush (closedInclusion S)
      (probabilityMap (lam.comp (closedInclusion S)) (probabilityStateOnClosed S hS χ hfull)) =
      probabilityMap lam χ := by
  rw [← probability_map_push,probability_state_on_closed_push]

lemma probability_push_closed_injective (hclosed : IsClosed S) :
    Function.Injective (probabilityPush (closedInclusion S)) := by
  intro μ ν he
  apply ProbabilityMeasure.toMeasure_injective
  have hm := congrArg (fun η : ProbabilityMeasure K => (η : Measure K).comap ((↑) : S → K)) he
  change ((μ : Measure S).map ((↑) : S → K)).comap ((↑) : S → K) =
    ((ν : Measure S).map ((↑) : S → K)).comap ((↑) : S → K) at hm
  simpa only [(MeasurableEmbedding.subtype_coe hclosed.measurableSet).comap_map] using hm

lemma probability_map_carried (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (hfull : (∀ᵐ x ∂(χ.1 : Measure K), x ∈ S) ∧ (∀ᵐ x ∂(χ.2 : Measure K), x ∈ S)) :
    (∀ᵐ x ∂((probabilityMap lam χ).1 : Measure K), x ∈ S) ∧
      (∀ᵐ x ∂((probabilityMap lam χ).2 : Measure K), x ∈ S) := by
  constructor
  · exact (probability_map_first_absolutelyContinuous lam χ).ae_le hfull.1
  · by_cases h : 0 < probabilityGrowthSq lam χ
    · simpa only [probabilityMap,dif_pos h] using hfull.1
    · simpa only [probabilityMap,dif_neg h] using hfull.2

lemma probability_map_on_closed (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (hfull : (∀ᵐ x ∂(χ.1 : Measure K), x ∈ S) ∧ (∀ᵐ x ∂(χ.2 : Measure K), x ∈ S)) :
    probabilityStateOnClosed S hS (probabilityMap lam χ) (probability_map_carried S lam χ hfull) =
      probabilityMap (lam.comp (closedInclusion S)) (probabilityStateOnClosed S hS χ hfull) := by
  have he : probabilityStatePush (closedInclusion S)
      (probabilityStateOnClosed S hS (probabilityMap lam χ) (probability_map_carried S lam χ hfull)) =
      probabilityStatePush (closedInclusion S)
        (probabilityMap (lam.comp (closedInclusion S)) (probabilityStateOnClosed S hS χ hfull)) := by
    rw [probability_state_on_closed_push,probability_map_on_closed_push]
  exact Prod.ext (probability_push_closed_injective S hS (congrArg Prod.fst he))
    (probability_push_closed_injective S hS (congrArg Prod.snd he))

end Closed
end BB
