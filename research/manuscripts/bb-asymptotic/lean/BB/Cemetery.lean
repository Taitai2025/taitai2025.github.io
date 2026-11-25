import BB.ExtendedLog
import Mathlib.Dynamics.Ergodic.Ergodic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# An isolated terminal state and invariant measures

The disjoint sum X ⊕ Unit realizes the paper's cemetery point literally.
Nonregular states are sent there in one step. The regular dynamics are not
modified. All measure reductions are proved, including zero terminal mass
whenever the extended logarithmic integral is finite.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal

abbrev Cemetery (X : Type*) := X ⊕ Unit

def cemeteryPoint {X : Type*} : Cemetery X := Sum.inr ()

def killedMap {X : Type*} (T : X → X) (r : X → ℝ) : Cemetery X → Cemetery X
  | Sum.inl x => if 0 < r x then Sum.inl (T x) else cemeteryPoint
  | Sum.inr _ => cemeteryPoint

def killedMultiplier {X : Type*} (r : X → ℝ) : Cemetery X → ℝ := Sum.elim r (fun _ => 0)

def cemeteryProjection {X : Type*} (x₀ : X) : Cemetery X → X := Sum.elim id (fun _ => x₀)

variable {X : Type*} [MeasurableSpace X]

instance cemetery_measurableSingletonClass [MeasurableSingletonClass X] :
    MeasurableSingletonClass (Cemetery X) := by
  constructor
  intro s
  cases s with
  | inl x =>
    simpa only [Set.image_singleton] using
      (measurableSet_inl_image (β := Unit)).mpr (measurableSet_singleton x)
  | inr u =>
    simpa only [Set.image_singleton] using
      (measurableSet_inr_image (α := X)).mpr (measurableSet_singleton u)

theorem killedMultiplier_measurable (r : X → ℝ) (hr : Measurable r) :
    Measurable (killedMultiplier r) := hr.sumElim measurable_const

theorem cemeteryProjection_measurable (x₀ : X) : Measurable (cemeteryProjection x₀) :=
  measurable_id.sumElim measurable_const

theorem killedMap_measurable (T : X → X) (r : X → ℝ)
    (hT : Measurable T) (hr : Measurable r) : Measurable (killedMap T r) := by
  apply measurable_sum
  · exact Measurable.ite (measurableSet_lt measurable_const hr)
      (measurable_inl.comp hT) measurable_const
  · exact measurable_const

@[simp] theorem killedMap_point (T : X → X) (r : X → ℝ) :
    killedMap T r (cemeteryPoint : Cemetery X) = cemeteryPoint := rfl

@[simp] theorem killedMultiplier_point (r : X → ℝ) :
    killedMultiplier r (cemeteryPoint : Cemetery X) = 0 := rfl

theorem killedMap_regular (T : X → X) (r : X → ℝ) (x : X) (hx : 0 < r x) :
    killedMap T r (Sum.inl x) = Sum.inl (T x) := if_pos hx

theorem killedMap_singular (T : X → X) (r : X → ℝ) (x : X) (hx : ¬ 0 < r x) :
    killedMap T r (Sum.inl x) = cemeteryPoint := if_neg hx

theorem killedMap_preimage_point (T : X → X) (r : X → ℝ) :
    killedMap T r ⁻¹' {cemeteryPoint} =
      (Sum.inl '' {x | ¬ 0 < r x}) ∪ {cemeteryPoint} := by
  ext s
  cases s with
  | inl x =>
    by_cases hx : 0 < r x
    · simp [killedMap, hx, cemeteryPoint]
    · simp [killedMap, hx, cemeteryPoint, not_lt.mp hx]
  | inr u => cases u; simp [killedMap, cemeteryPoint]

/-- Every finite invariant measure gives zero mass to the singular states,
without any integrability hypothesis. -/
theorem killed_invariant_singular_null (T : X → X) (r : X → ℝ)
    (_hr : Measurable r) (μ : Measure (Cemetery X)) [IsFiniteMeasure μ]
    (hT : MeasurePreserving (killedMap T r) μ μ) :
    μ (Sum.inl '' {x | ¬ 0 < r x}) = 0 := by
  have hpoint : MeasurableSet ({cemeteryPoint} : Set (Cemetery X)) := by
    have he : (Sum.inr '' ({()} : Set Unit) : Set (Cemetery X)) = {cemeteryPoint} := by
      simp [cemeteryPoint]
    rw [← he]
    exact measurableSet_inr_image.mpr (measurableSet_singleton ())
  have hd : Disjoint (Sum.inl '' {x | ¬ 0 < r x} : Set (Cemetery X)) {cemeteryPoint} := by
    simp only [disjoint_singleton_right, mem_image, mem_setOf_eq, cemeteryPoint]
    simp
  have he := hT.measure_preimage hpoint
  rw [killedMap_preimage_point, measure_union hd hpoint] at he
  have he' : μ {cemeteryPoint} + μ (Sum.inl '' {x | ¬ 0 < r x}) = μ {cemeteryPoint} + 0 := by
    simpa only [add_zero, zero_add, add_comm] using he
  exact (ENNReal.add_right_inj (measure_ne_top μ _)).mp he'

theorem killed_regular_ae_not_point (r : X → ℝ) (μ : Measure (Cemetery X))
    (hregular : ∀ᵐ s ∂μ, 0 < killedMultiplier r s) :
    ∀ᵐ s ∂μ, s ≠ cemeteryPoint := by
  filter_upwards [hregular] with s hs
  intro he
  subst s
  exact (lt_irrefl (0 : ℝ)) hs

/-- The projection is inverse to the regular inclusion almost everywhere. -/
theorem cemetery_inclusion_projection_ae (r : X → ℝ) (x₀ : X)
    (μ : Measure (Cemetery X)) (hregular : ∀ᵐ s ∂μ, 0 < killedMultiplier r s) :
    (fun s => Sum.inl (cemeteryProjection x₀ s)) =ᵐ[μ] (fun s => s) := by
  filter_upwards [hregular] with s hs
  cases s with
  | inl x => rfl
  | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)

def cemeteryBaseMeasure (x₀ : X) (μ : Measure (Cemetery X)) : Measure X :=
  μ.map (cemeteryProjection x₀)

instance cemeteryBaseMeasure_probability (x₀ : X) (μ : Measure (Cemetery X))
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (cemeteryBaseMeasure x₀ μ) :=
  isProbabilityMeasure_map (cemeteryProjection_measurable x₀).aemeasurable

theorem cemetery_base_lift (r : X → ℝ) (x₀ : X) (μ : Measure (Cemetery X))
    (hregular : ∀ᵐ s ∂μ, 0 < killedMultiplier r s) :
    (cemeteryBaseMeasure x₀ μ).map Sum.inl = μ := by
  rw [cemeteryBaseMeasure, Measure.map_map measurable_inl (cemeteryProjection_measurable x₀)]
  calc
    _ = μ.map (fun s => s) := Measure.map_congr (cemetery_inclusion_projection_ae r x₀ μ hregular)
    _ = μ := Measure.map_id

theorem cemetery_base_preserving (T : X → X) (r : X → ℝ) (hTmeas : Measurable T)
    (x₀ : X) (μ : Measure (Cemetery X))
    (hT : MeasurePreserving (killedMap T r) μ μ)
    (hregular : ∀ᵐ s ∂μ, 0 < killedMultiplier r s) :
    MeasurePreserving T (cemeteryBaseMeasure x₀ μ) (cemeteryBaseMeasure x₀ μ) := by
  have hp := cemeteryProjection_measurable x₀
  have hcomm : (T ∘ cemeteryProjection x₀) =ᵐ[μ]
      (cemeteryProjection x₀ ∘ killedMap T r) := by
    filter_upwards [hregular] with s hs
    cases s with
    | inl x => simp only [Function.comp_apply, cemeteryProjection, Sum.elim_inl,
        killedMap_regular T r x hs, id_eq]
    | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)
  refine ⟨hTmeas, ?_⟩
  rw [cemeteryBaseMeasure, Measure.map_map hTmeas hp, Measure.map_congr hcomm,
    ← Measure.map_map hp hT.measurable, hT.map_eq]

theorem cemetery_base_regular (r : X → ℝ) (hr : Measurable r) (x₀ : X)
    (μ : Measure (Cemetery X)) (hregular : ∀ᵐ s ∂μ, 0 < killedMultiplier r s) :
    ∀ᵐ x ∂cemeteryBaseMeasure x₀ μ, 0 < r x := by
  rw [cemeteryBaseMeasure, ae_map_iff (cemeteryProjection_measurable x₀).aemeasurable
    (measurableSet_lt measurable_const hr)]
  filter_upwards [hregular] with s hs
  cases s with
  | inl x => exact hs
  | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)

theorem cemetery_log_integrable_transfer (r : X → ℝ) (hr : Measurable r) (x₀ : X)
    (μ : Measure (Cemetery X)) (hregular : ∀ᵐ s ∂μ, 0 < killedMultiplier r s)
    (hf : Integrable (fun s => Real.log (killedMultiplier r s)) μ) :
    Integrable (fun x => Real.log (r x)) (cemeteryBaseMeasure x₀ μ) ∧
      (∫ s, Real.log (killedMultiplier r s) ∂μ) =
        ∫ x, Real.log (r x) ∂cemeteryBaseMeasure x₀ μ := by
  have hm : AEStronglyMeasurable (fun x => Real.log (r x)) (cemeteryBaseMeasure x₀ μ) :=
    (Real.measurable_log.comp hr).aestronglyMeasurable
  have hp := cemeteryProjection_measurable x₀
  have he : (fun s => Real.log (killedMultiplier r s)) =ᵐ[μ]
      (fun s => Real.log (r (cemeteryProjection x₀ s))) := by
    filter_upwards [hregular] with s hs
    cases s with
    | inl x => rfl
    | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)
  constructor
  · exact (integrable_map_measure hm hp.aemeasurable).mpr (hf.congr he)
  · rw [cemeteryBaseMeasure, integral_map hp.aemeasurable hm]
    exact integral_congr_ae he

end BB
