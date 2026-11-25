import BB.InvariantPartition
import BB.Cemetery

/-!
# A common finite support for an ergodic BB state law

Ergodicity is used only for a finite measurable partition. The update and
delayed-shift equations are proved elsewhere for the actual state map; here
they imply a common positive support with at least two distinct values.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set

variable {X : Type*} [MeasurableSpace X]

theorem ergodic_finite_partition_full {κ : Type*} [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Ergodic T μ)
    (A : κ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hcover : ∀ x, ∃ i, x ∈ A i)
    (hinv : ∀ i, ∀ᵐ x ∂μ, x ∈ A i ↔ T x ∈ A i) :
    ∃ i, ∀ᵐ x ∂μ, x ∈ A i := by
  classical
  by_contra hnot
  have hnull : ∀ i, ∀ᵐ x ∂μ, x ∉ A i := by
    intro i
    have heq : T ⁻¹' A i =ᵐ[μ] A i := by
      filter_upwards [hinv i] with x hx
      exact propext hx.symm
    rcases hT.quasiErgodic.ae_empty_or_univ' (hA i) heq with hz | hf
    · exact eventuallyEq_empty.mp hz
    · exact (hnot ⟨i, eventuallyEq_univ.mp hf⟩).elim
  obtain ⟨x,hx⟩ := (ae_all_iff.mpr hnull).exists
  obtain ⟨i,hi⟩ := hcover x
  exact hx i hi

variable {ι : Type*} [Fintype ι]

theorem ergodic_bb_common_support
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X) (hT : Ergodic T μ)
    (lam : ι → ℝ) (hpositive : ∀ i, 0 < lam i)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hregular : ∀ᵐ x ∂μ, 0 < growthSq lam (w x) (z x))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x) :
    ∃ J : Finset ι, 2 ≤ J.card ∧ ∀ᵐ x ∂μ,
      (∀ i, w x i ≠ 0 ↔ i ∈ J) ∧ (∀ i, z x i ≠ 0 ↔ i ∈ J) := by
  classical
  obtain ⟨J,hJ⟩ := ergodic_finite_partition_full μ T hT (supportClass w)
    (supportClass_measurable w hwmeas) (supportClass_cover w)
    (supportClass_invariant_ae μ T hT.toMeasurePreserving lam w z hwmeas hupdate)
  have hcommon := bb_consecutive_supports_equal_ae μ T hT.toMeasurePreserving lam w z
    hwmeas hzmeas hupdate hshift
  have hboth : ∀ᵐ x ∂μ,
      (∀ i, w x i ≠ 0 ↔ i ∈ J) ∧ (∀ i, z x i ≠ 0 ↔ i ∈ J) := by
    filter_upwards [hJ,hcommon] with x hx hc
    refine ⟨hx, fun i => ?_⟩
    exact (not_congr (hc i)).symm.trans (hx i)
  obtain ⟨x,hx,hR⟩ := (hboth.and hregular).exists
  obtain ⟨lo,hlo,hi,hhi,hab,_⟩ := regular_support_endpoints lam (w x) (z x) J
    hpositive (hw x) (hz x) hx.1 hx.2 hR
  have hne : lo ≠ hi := by intro he; rw [he] at hab; exact lt_irrefl _ hab
  have hcard : 1 < J.card := Finset.one_lt_card.mpr ⟨lo,hlo,hi,hhi,hne⟩
  exact ⟨J, by omega, hboth⟩

end BB
