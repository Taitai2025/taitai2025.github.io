import BB.HilbertProbability
import Mathlib.Topology.TietzeExtension
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Restricting weak convergence to a common closed support

The restriction is an actual probability measure on the closed subtype, built
with `Measure.comap`. Tietze extension proves weak convergence on that subtype;
Portmanteau then applies to its relative continuity sets. In particular the
boundary in the last theorem is the relative subtype boundary.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction
variable {K : Type*} [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]

lemma probability_subtype_integral (S : Set K) (ν : ProbabilityMeasure S) (f : K →ᵇ ℝ) :
    (∫ x, f x ∂(ν.map measurable_subtype_coe.aemeasurable : Measure K)) =
      ∫ x : S, f x ∂(ν : Measure S) := by
  change (∫ x, f x ∂(ν : Measure S).map Subtype.val) = _
  exact integral_map measurable_subtype_coe.aemeasurable f.continuous.measurable.aestronglyMeasurable

/-- Weak convergence after closed inclusion implies weak convergence on the
relative space; there is no missing extension hypothesis. -/
theorem probability_subtype_tendsto_of_map [NormalSpace K]
    (S : Set K) (hS : IsClosed S) {J : Type*} {l : Filter J}
    (νs : J → ProbabilityMeasure S) (ν : ProbabilityMeasure S)
    (hlim : Tendsto (fun j => (νs j).map measurable_subtype_coe.aemeasurable) l
      (𝓝 (ν.map measurable_subtype_coe.aemeasurable))) :
    Tendsto νs l (𝓝 ν) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  obtain ⟨g,_hnorm,hg⟩ := f.exists_norm_eq_restrict_eq_of_closed hS
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) g
  simp only [probability_subtype_integral] at h
  have he : (fun x : S => g x) = f := congrArg DFunLike.coe hg
  simpa only [he] using h

def probabilityOnClosed (ν : ProbabilityMeasure K) (S : Set K) (hS : IsClosed S)
    (hfull : ∀ᵐ x ∂(ν : Measure K), x ∈ S) : ProbabilityMeasure S :=
  ⟨(ν : Measure K).comap Subtype.val,
    (MeasurableEmbedding.subtype_coe hS.measurableSet).isProbabilityMeasure_comap
      (by simpa only [Subtype.range_coe] using hfull)⟩

lemma probability_on_closed_map (ν : ProbabilityMeasure K) (S : Set K) (hS : IsClosed S)
    (hfull : ∀ᵐ x ∂(ν : Measure K), x ∈ S) :
    (probabilityOnClosed ν S hS hfull).map measurable_subtype_coe.aemeasurable = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((ν : Measure K).comap Subtype.val).map ((↑) : S → K) = (ν : Measure K)
  rw [map_comap_subtype_coe hS.measurableSet,Measure.restrict_eq_self_of_ae_mem hfull]

/-- The manuscript's restricted-weak lemma, with all subtype measures
constructed from the original full-support hypotheses. -/
theorem probability_closed_restriction_tendsto [NormalSpace K]
    (S : Set K) (hS : IsClosed S) {J : Type*} {l : Filter J}
    (νs : J → ProbabilityMeasure K) (ν : ProbabilityMeasure K)
    (hfulls : ∀ j, ∀ᵐ x ∂(νs j : Measure K), x ∈ S)
    (hfull : ∀ᵐ x ∂(ν : Measure K), x ∈ S)
    (hlim : Tendsto νs l (𝓝 ν)) :
    Tendsto (fun j => probabilityOnClosed (νs j) S hS (hfulls j)) l
      (𝓝 (probabilityOnClosed ν S hS hfull)) := by
  apply probability_subtype_tendsto_of_map S hS
  simpa only [probability_on_closed_map] using hlim

/-- Continuity sets use the relative boundary in `S`, so atoms at the outer
endpoints of the ambient compact set cause no additional obstruction. -/
theorem probability_relative_continuity_set_tendsto
    [TopologicalSpace.PseudoMetrizableSpace K] [NormalSpace K] [HasOuterApproxClosed K]
    (S : Set K) (hS : IsClosed S) {J : Type*} {l : Filter J}
    (νs : J → ProbabilityMeasure K) (ν : ProbabilityMeasure K)
    (hfulls : ∀ j, ∀ᵐ x ∂(νs j : Measure K), x ∈ S)
    (hfull : ∀ᵐ x ∂(ν : Measure K), x ∈ S)
    (hlim : Tendsto νs l (𝓝 ν)) (D : Set S)
    (hboundary : (probabilityOnClosed ν S hS hfull : Measure S) (frontier D) = 0) :
    Tendsto (fun j => (probabilityOnClosed (νs j) S hS (hfulls j) : Measure S) D) l
      (𝓝 ((probabilityOnClosed ν S hS hfull : Measure S) D)) := by
  letI : PseudoMetricSpace K := TopologicalSpace.pseudoMetrizableSpacePseudoMetric K
  exact ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    (probability_closed_restriction_tendsto S hS νs ν hfulls hfull hlim) hboundary

end BB
