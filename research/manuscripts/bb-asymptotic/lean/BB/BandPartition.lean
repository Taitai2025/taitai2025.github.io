import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Instances.Real
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-! # Finite continuous spectral bands

This constructs a genuine finite nonnegative partition of unity of any compact
metric space, with every nonzero band value lying within a prescribed radius
of its center.  In particular it applies to a closed spectral interval.
-/

namespace BB
noncomputable section
open Set
open scoped BigOperators

theorem finite_band_partition {K : Type*} [MetricSpace K] [CompactSpace K]
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset K, ∃ φ : s → C(K,ℝ),
      (∀ i x, 0 ≤ φ i x) ∧ (∑ i, φ i) = 1 ∧
      (∀ i x, φ i x ≠ 0 → dist x (i : K) < ε) := by
  classical
  have hcover : (univ : Set K) ⊆ ⋃ x : K, Metric.ball x ε := by
    intro x _
    exact mem_iUnion.mpr ⟨x,Metric.mem_ball_self hε⟩
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover (fun x : K => Metric.ball x ε)
    (fun _ => Metric.isOpen_ball) hcover
  have hcover' : (univ : Set K) ⊆ ⋃ i : s, Metric.ball (i : K) ε := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion.mpr ⟨⟨i,hi⟩,hxi⟩
  obtain ⟨φ,hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    (fun i : s => Metric.ball (i : K) ε) (fun _ => Metric.isOpen_ball) hcover'
  refine ⟨s,(fun i => φ i),(fun i x => φ.nonneg i x),?_,?_⟩
  · ext x
    simpa only [ContinuousMap.sum_apply,ContinuousMap.one_apply,finsum_eq_sum_of_fintype] using
      φ.sum_eq_one (mem_univ x)
  · intro i x hx
    exact hφ i (subset_tsupport _ (Function.mem_support.mpr hx))

theorem interval_band_partition (A B ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset (Icc A B), ∃ φ : s → C(Icc A B,ℝ),
      (∀ i x, 0 ≤ φ i x) ∧ (∑ i, φ i) = 1 ∧
      (∀ i x, φ i x ≠ 0 → |x.1-(i : Icc A B).1| < ε) := by
  classical
  obtain ⟨s,φ,hpos,hsum,hsupp⟩ := finite_band_partition (K := Icc A B) ε hε
  refine ⟨s,φ,hpos,hsum,?_⟩
  intro i x hx
  simpa only [Subtype.dist_eq,Real.dist_eq] using hsupp i x hx

end
end BB
