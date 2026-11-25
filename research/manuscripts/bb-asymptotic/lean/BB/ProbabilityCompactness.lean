import BB.RieszRepresentation
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.Sequences

/-!
# Weak compactness of actual probability measures

The compact positive-functional model and the proved compact Riesz theorem
identify the library's weak probability-measure topology with a compact space.
The topology is not replaced or assumed compact.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
  [NormalSpace K] [MeasurableSpace K] [BorelSpace K] [HasOuterApproxClosed K]

/-- The Riesz inverse is continuous for the actual weak topology of probability
measures, because each continuous test integral is an evaluation of the state. -/
theorem representingProbability_continuous :
    Continuous (representingProbability : PositiveState K → ProbabilityMeasure K) := by
  apply continuous_iff_continuousAt.mpr
  intro L
  apply (probability_functional_tendsto_iff representingProbability
    (representingProbability L)).mp
  simpa only [probabilityFunctional_representing] using
    (tendsto_id : Tendsto (fun L : PositiveState K => L) (𝓝 L) (𝓝 L))

/-- Actual weak probability measures and positive normalized continuous
functionals are homeomorphic. Both inverse identities follow from proved Riesz
representation and weak-measure uniqueness. -/
def probabilityFunctionalHomeomorph : ProbabilityMeasure K ≃ₜ PositiveState K where
  toFun := probabilityFunctional
  invFun := representingProbability
  left_inv ν := probability_functional_injective
    (probabilityFunctional_representing (probabilityFunctional ν))
  right_inv := probabilityFunctional_representing
  continuous_toFun := probability_functional_continuous
  continuous_invFun := representingProbability_continuous

@[simp] theorem probabilityFunctionalHomeomorph_apply (ν : ProbabilityMeasure K) :
    probabilityFunctionalHomeomorph ν = probabilityFunctional ν := rfl

@[simp] theorem probabilityFunctionalHomeomorph_symm_apply (L : PositiveState K) :
    probabilityFunctionalHomeomorph.symm L = representingProbability L := rfl

/-- Weak compactness is transported from the proved Banach--Alaoglu compact
positive-state space through the actual Riesz homeomorphism. -/
instance probabilityMeasureCompactSpace : CompactSpace (ProbabilityMeasure K) :=
  (probabilityFunctionalHomeomorph (K := K)).symm.compactSpace

section Sequential
variable {M : Type*} [MetricSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]

/-- Every sequence of actual probability measures on a compact metric Borel
space has a weakly convergent strictly increasing subsequence. The subsequence
is obtained after proving compactness above and using the library's proved
Levy--Prokhorov metrization of weak convergence. -/
theorem probabilityMeasure_tendsto_subseq (νs : ℕ → ProbabilityMeasure M) :
    ∃ (ν : ProbabilityMeasure M) (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (νs ∘ φ) atTop (𝓝 ν) :=
  CompactSpace.tendsto_subseq νs

end Sequential

end BB
