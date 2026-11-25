import BB.WeakLimitTools
import BB.ExtendedLog

/-!
# Extended integrals of functions bounded above

The codomain includes minus infinity. A finite upper bound converts the
integral into the ordinary nonnegative Lebesgue integral of a loss. The
conversion is pointwise exact and independent of the chosen valid bound.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

variable {X : Type*}

def upperDefect (C : ℝ) (f : X → EReal) (x : X) : ℝ≥0∞ :=
  if f x = ⊥ then ⊤ else ENNReal.ofReal (C - (f x).toReal)

theorem upper_defect_top_iff (C : ℝ) (f : X → EReal) (x : X) :
    upperDefect C f x = ⊤ ↔ f x = ⊥ := by
  by_cases h : f x = ⊥ <;> simp [upperDefect, h]

theorem upper_defect_lt_top_iff (C : ℝ) (f : X → EReal) (x : X) :
    upperDefect C f x < ⊤ ↔ f x ≠ ⊥ := by
  rw [lt_top_iff_ne_top, ne_eq, upper_defect_top_iff]

theorem upper_defect_threshold (C : ℝ) (f : X → EReal)
    (hC : ∀ x, f x ≤ (C : EReal)) (x : X) (y : ℝ≥0∞) (hy : y ≠ ⊤) :
    y < upperDefect C f x ↔ f x < ((C - y.toReal : ℝ) : EReal) := by
  by_cases hb : f x = ⊥
  · rw [upperDefect, if_pos hb, hb]
    exact iff_of_true (lt_top_iff_ne_top.mpr hy) (EReal.bot_lt_coe _)
  · have ht : f x ≠ ⊤ := ne_of_lt ((hC x).trans_lt (EReal.coe_lt_top C))
    have he := EReal.coe_toReal ht hb
    rw [upperDefect, if_neg hb, ← he, EReal.coe_lt_coe_iff]
    rw [← ENNReal.ofReal_toReal hy, ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg]
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, EReal.toReal_coe]
    constructor <;> intro h <;> linarith

theorem upper_defect_reconstruction (C : ℝ) (f : X → EReal)
    (hC : ∀ x, f x ≤ (C : EReal)) (x : X) :
    (C : EReal) - (upperDefect C f x : EReal) = f x := by
  by_cases hb : f x = ⊥
  · simp [upperDefect, hb]
  · have ht : f x ≠ ⊤ := ne_of_lt ((hC x).trans_lt (EReal.coe_lt_top C))
    have he := EReal.coe_toReal ht hb
    have hr : (f x).toReal ≤ C := by
      exact EReal.coe_le_coe_iff.mp (he ▸ hC x)
    rw [upperDefect, if_neg hb, EReal.coe_ennreal_ofReal,
      max_eq_left (sub_nonneg.mpr hr), ← EReal.coe_sub]
    simpa only [sub_sub_cancel] using he

theorem upper_defect_lowerSemicontinuous [TopologicalSpace X]
    (C : ℝ) (f : X → EReal) (hC : ∀ x, f x ≤ (C : EReal))
    (hf : UpperSemicontinuous f) : LowerSemicontinuous (upperDefect C f) := by
  apply lowerSemicontinuous_iff_isOpen_preimage.mpr
  intro y
  by_cases hy : y = ⊤
  · simp [hy]
  · have he : (upperDefect C f ⁻¹' Ioi y) = f ⁻¹' Iio ((C - y.toReal : ℝ) : EReal) := by
      ext x
      exact upper_defect_threshold C f hC x y hy
    rw [he]
    exact hf.isOpen_preimage _

variable [MeasurableSpace X]

def boundedAboveIntegral (C : ℝ) (f : X → EReal) (μ : Measure X) : EReal :=
  (C : EReal) - ((∫⁻ x, upperDefect C f x ∂μ) : EReal)

theorem bounded_above_integral_eq_bot_iff (C : ℝ) (f : X → EReal) (μ : Measure X) :
    boundedAboveIntegral C f μ = ⊥ ↔ (∫⁻ x, upperDefect C f x ∂μ) = ⊤ := by
  simp [boundedAboveIntegral, sub_eq_add_neg, EReal.add_eq_bot_iff]

theorem upper_defect_measurable (C : ℝ) (f : X → EReal) (hf : Measurable f) :
    Measurable (upperDefect C f) := by
  apply Measurable.ite ((measurableSet_singleton (⊥ : EReal)).preimage hf)
  · exact measurable_const
  · exact (measurable_const.sub hf.ereal_toReal).ennreal_ofReal

theorem bounded_above_integral_finite_formula (C : ℝ) (f : X → EReal) (μ : Measure X)
    (hfin : (∫⁻ x, upperDefect C f x ∂μ) ≠ ⊤) :
    boundedAboveIntegral C f μ =
      ((C - (∫⁻ x, upperDefect C f x ∂μ).toReal : ℝ) : EReal) := by
  have he : (((∫⁻ x, upperDefect C f x ∂μ).toReal : ℝ) : EReal) =
      ((∫⁻ x, upperDefect C f x ∂μ) : EReal) := by
    simpa only [EReal.toReal_coe_ennreal] using
      EReal.coe_toReal (by simpa using hfin) (EReal.coe_ennreal_ne_bot _)
  simp only [boundedAboveIntegral, EReal.coe_sub, he]

theorem bounded_above_integral_finite_reduction (C : ℝ) (f : X → EReal)
    (hf : Measurable f) (hC : ∀ x, f x ≤ (C : EReal))
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hfin : boundedAboveIntegral C f μ ≠ ⊥) :
    (∀ᵐ x ∂μ, f x ≠ ⊥) ∧ Integrable (fun x => (f x).toReal) μ ∧
      boundedAboveIntegral C f μ = ((∫ x, (f x).toReal ∂μ : ℝ) : EReal) := by
  have hq := upper_defect_measurable C f hf
  have hqfin : (∫⁻ x, upperDefect C f x ∂μ) ≠ ⊤ :=
    mt (bounded_above_integral_eq_bot_iff C f μ).mpr hfin
  have hae : ∀ᵐ x ∂μ, f x ≠ ⊥ := by
    filter_upwards [ae_lt_top hq hqfin] with x hx
    exact (upper_defect_lt_top_iff C f x).mp hx
  have he : (fun x => (upperDefect C f x).toReal) =ᵐ[μ]
      (fun x => C - (f x).toReal) := by
    filter_upwards [hae] with x hx
    have ht : f x ≠ ⊤ := ne_of_lt ((hC x).trans_lt (EReal.coe_lt_top C))
    have hr : (f x).toReal ≤ C := by
      exact EReal.coe_le_coe_iff.mp ((EReal.coe_toReal ht hx) ▸ hC x)
    simp only [upperDefect, if_neg hx, ENNReal.toReal_ofReal (sub_nonneg.mpr hr)]
  have hiq := integrable_toReal_of_lintegral_ne_top hq.aemeasurable hqfin
  have hid : Integrable (fun x => C - (f x).toReal) μ := hiq.congr he
  have hif : Integrable (fun x => (f x).toReal) μ := by
    have h := (integrable_const C).sub hid
    exact h.congr (eventually_of_forall (fun x => by dsimp; ring))
  refine ⟨hae, hif, ?_⟩
  have hi : (∫⁻ x, upperDefect C f x ∂μ).toReal = C - ∫ x, (f x).toReal ∂μ := by
    rw [← integral_toReal hq.aemeasurable (ae_lt_top hq hqfin), integral_congr_ae he,
      integral_sub (integrable_const C) hif]
    simp
  rw [bounded_above_integral_finite_formula C f μ hqfin, hi]
  congr 1
  ring

theorem bounded_above_integral_of_integrable (C : ℝ) (f : X → EReal)
    (hf : Measurable f) (hC : ∀ x, f x ≤ (C : EReal))
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hfinite : ∀ᵐ x ∂μ, f x ≠ ⊥) (hi : Integrable (fun x => (f x).toReal) μ) :
    boundedAboveIntegral C f μ = ((∫ x, (f x).toReal ∂μ : ℝ) : EReal) := by
  have he : upperDefect C f =ᵐ[μ] (fun x => ENNReal.ofReal (C - (f x).toReal)) := by
    filter_upwards [hfinite] with x hx
    exact if_neg hx
  have hn : 0 ≤ᵐ[μ] (fun x => C - (f x).toReal) := by
    filter_upwards [hfinite] with x hx
    have ht : f x ≠ ⊤ := ne_of_lt ((hC x).trans_lt (EReal.coe_lt_top C))
    exact sub_nonneg.mpr (EReal.coe_le_coe_iff.mp ((EReal.coe_toReal ht hx) ▸ hC x))
  have hfin : (∫⁻ x, upperDefect C f x ∂μ) ≠ ⊤ := by
    rw [lintegral_congr_ae he]
    exact ((hasFiniteIntegral_iff_ofReal hn).mp ((integrable_const C).sub hi).hasFiniteIntegral).ne
  exact (bounded_above_integral_finite_reduction C f hf hC μ
    (mt (bounded_above_integral_eq_bot_iff C f μ).mp hfin)).2.2

theorem bounded_above_integral_independent_bound (C D : ℝ) (f : X → EReal)
    (hf : Measurable f) (hC : ∀ x, f x ≤ (C : EReal)) (hD : ∀ x, f x ≤ (D : EReal))
    (μ : Measure X) [IsProbabilityMeasure μ] :
    boundedAboveIntegral C f μ = boundedAboveIntegral D f μ := by
  by_cases hc : boundedAboveIntegral C f μ = ⊥
  · by_cases hd : boundedAboveIntegral D f μ = ⊥
    · exact hc.trans hd.symm
    · obtain ⟨hp, hi, _⟩ := bounded_above_integral_finite_reduction D f hf hD μ hd
      have he := bounded_above_integral_of_integrable C f hf hC μ hp hi
      rw [hc] at he
      exact False.elim ((EReal.coe_ne_bot (∫ x, (f x).toReal ∂μ : ℝ)) he.symm)
  · obtain ⟨hp, hi, he⟩ := bounded_above_integral_finite_reduction C f hf hC μ hc
    exact he.trans (bounded_above_integral_of_integrable D f hf hD μ hp hi).symm

@[simp] theorem upper_defect_extendedLog (C : ℝ) (r : X → ℝ) (x : X) :
    upperDefect C (fun y => extendedLog (r y)) x = logDefect r C x := by
  by_cases hx : 0 < r x <;> simp [upperDefect, extendedLog, logDefect, hx]

theorem bounded_above_integral_extendedLog (C : ℝ) (r : X → ℝ) (μ : Measure X) :
    boundedAboveIntegral C (fun y => extendedLog (r y)) μ = extendedLogIntegral r C μ := by
  simp only [boundedAboveIntegral, upper_defect_extendedLog, extendedLogIntegral]

end BB
