import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Topology.Instances.EReal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Extended logarithmic averages

The logarithm at a nonpositive multiplier is minus infinity. For a finite
upper bound C, its integral is defined by subtracting the nonnegative Lebesgue
integral of the defect from C. In particular, Lean's total real logarithm at
zero is never used to assign a finite average to a terminal state.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X]

def extendedLog (r : ℝ) : EReal := if 0 < r then (Real.log r : EReal) else ⊥

def logDefect (r : X → ℝ) (C : ℝ) (x : X) : ℝ≥0∞ :=
  if 0 < r x then ENNReal.ofReal (C - Real.log (r x)) else ⊤

/-- The genuine extended integral of a logarithm bounded above by C,
computed using the nonnegative Lebesgue integral of its defect. -/
def extendedLogIntegral (r : X → ℝ) (C : ℝ) (μ : Measure X) : EReal :=
  (C : EReal) - ((∫⁻ x, logDefect r C x ∂μ) : EReal)

theorem logDefect_measurable (r : X → ℝ) (hr : Measurable r) (C : ℝ) :
    Measurable (logDefect r C) := by
  apply Measurable.ite (measurableSet_lt measurable_const hr)
  · exact (measurable_const.sub (Real.measurable_log.comp hr)).ennreal_ofReal
  · exact measurable_const

theorem logDefect_lt_top_iff (r : X → ℝ) (C : ℝ) (x : X) :
    logDefect r C x < ⊤ ↔ 0 < r x := by
  by_cases hx : 0 < r x <;> simp [logDefect, hx]

theorem extendedLogIntegral_eq_bot_iff (r : X → ℝ) (C : ℝ) (μ : Measure X) :
    extendedLogIntegral r C μ = ⊥ ↔ (∫⁻ x, logDefect r C x ∂μ) = ⊤ := by
  simp [extendedLogIntegral, sub_eq_add_neg, EReal.add_eq_bot_iff]

theorem extendedLogIntegral_finite_formula (r : X → ℝ) (C : ℝ) (μ : Measure X)
    (hfin : (∫⁻ x, logDefect r C x ∂μ) ≠ ⊤) :
    extendedLogIntegral r C μ =
      ((C - (∫⁻ x, logDefect r C x ∂μ).toReal : ℝ) : EReal) := by
  have he : (((∫⁻ x, logDefect r C x ∂μ).toReal : ℝ) : EReal) =
      ((∫⁻ x, logDefect r C x ∂μ) : EReal) := by
    simpa only [EReal.toReal_coe_ennreal] using
      EReal.coe_toReal (by simpa using hfin) (EReal.coe_ennreal_ne_bot _)
  simp only [extendedLogIntegral, EReal.coe_sub, he]

theorem extendedLogIntegral_finite_reduction (r : X → ℝ) (hr : Measurable r)
    (C : ℝ) (hupper : ∀ x, 0 < r x → Real.log (r x) ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hfinite : extendedLogIntegral r C μ ≠ ⊥) :
    (∀ᵐ x ∂μ, 0 < r x) ∧ Integrable (fun x => Real.log (r x)) μ ∧
      extendedLogIntegral r C μ = ((∫ x, Real.log (r x) ∂μ : ℝ) : EReal) := by
  have hfin : (∫⁻ x, logDefect r C x ∂μ) ≠ ⊤ :=
    mt (extendedLogIntegral_eq_bot_iff r C μ).mpr hfinite
  have hq := logDefect_measurable r hr C
  have hqfinite := ae_lt_top hq hfin
  have hpos : ∀ᵐ x ∂μ, 0 < r x := by
    filter_upwards [hqfinite] with x hx
    exact (logDefect_lt_top_iff r C x).mp hx
  have hdef : (fun x => (logDefect r C x).toReal) =ᵐ[μ]
      (fun x => C - Real.log (r x)) := by
    filter_upwards [hpos] with x hx
    simp only [logDefect, if_pos hx, ENNReal.toReal_ofReal (sub_nonneg.mpr (hupper x hx))]
  have hiq := integrable_toReal_of_lintegral_ne_top hq.aemeasurable hfin
  have hid : Integrable (fun x => C - Real.log (r x)) μ := hiq.congr hdef
  have hilog : Integrable (fun x => Real.log (r x)) μ := by
    have h := (integrable_const C).sub hid
    exact h.congr (eventually_of_forall (fun x => by dsimp; ring))
  refine ⟨hpos, hilog, ?_⟩
  have he : (∫⁻ x, logDefect r C x ∂μ).toReal = C - ∫ x, Real.log (r x) ∂μ := by
    rw [← integral_toReal hq.aemeasurable hqfinite, integral_congr_ae hdef,
      integral_sub (integrable_const C) hilog]
    simp
  rw [extendedLogIntegral_finite_formula r C μ hfin, he]
  congr 1
  ring

theorem extendedLogIntegral_of_integrable (r : X → ℝ) (hr : Measurable r)
    (C : ℝ) (hupper : ∀ x, 0 < r x → Real.log (r x) ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 < r x) (hf : Integrable (fun x => Real.log (r x)) μ) :
    extendedLogIntegral r C μ = ((∫ x, Real.log (r x) ∂μ : ℝ) : EReal) := by
  have hdef : logDefect r C =ᵐ[μ] (fun x => ENNReal.ofReal (C - Real.log (r x))) := by
    filter_upwards [hpos] with x hx
    exact if_pos hx
  have hnonneg : 0 ≤ᵐ[μ] (fun x => C - Real.log (r x)) := by
    filter_upwards [hpos] with x hx
    exact sub_nonneg.mpr (hupper x hx)
  have hfin : (∫⁻ x, logDefect r C x ∂μ) ≠ ⊤ := by
    rw [lintegral_congr_ae hdef]
    exact ((hasFiniteIntegral_iff_ofReal hnonneg).mp
      ((integrable_const C).sub hf).hasFiniteIntegral).ne
  exact (extendedLogIntegral_finite_reduction r hr C hupper μ
    (mt (extendedLogIntegral_eq_bot_iff r C μ).mp hfin)).2.2

/-- This dichotomy discharges every nonintegrable and terminal case before
applying an ordinary real-valued invariant-average theorem. -/
theorem extendedLogIntegral_dichotomy (r : X → ℝ) (hr : Measurable r)
    (C : ℝ) (hupper : ∀ x, 0 < r x → Real.log (r x) ≤ C)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    extendedLogIntegral r C μ = ⊥ ∨
      ((∀ᵐ x ∂μ, 0 < r x) ∧ Integrable (fun x => Real.log (r x)) μ ∧
        extendedLogIntegral r C μ = ((∫ x, Real.log (r x) ∂μ : ℝ) : EReal)) := by
  by_cases h : extendedLogIntegral r C μ = ⊥
  · exact Or.inl h
  · exact Or.inr (extendedLogIntegral_finite_reduction r hr C hupper μ h)

/-- The choice of a valid finite upper bound does not change the integral. -/
theorem extendedLogIntegral_independent_bound (r : X → ℝ) (hr : Measurable r)
    (C D : ℝ) (hC : ∀ x, 0 < r x → Real.log (r x) ≤ C)
    (hD : ∀ x, 0 < r x → Real.log (r x) ≤ D)
    (μ : Measure X) [IsProbabilityMeasure μ] :
    extendedLogIntegral r C μ = extendedLogIntegral r D μ := by
  rcases extendedLogIntegral_dichotomy r hr C hC μ with hbot | ⟨hp,hf,he⟩
  · rcases extendedLogIntegral_dichotomy r hr D hD μ with hbot' | ⟨hp,hf,_⟩
    · exact hbot.trans hbot'.symm
    · have he := extendedLogIntegral_of_integrable r hr C hC μ hp hf
      rw [hbot] at he
      exact False.elim ((EReal.coe_ne_bot (∫ x, Real.log (r x) ∂μ : ℝ)) he.symm)
  · exact he.trans (extendedLogIntegral_of_integrable r hr D hD μ hp hf).symm

end BB
