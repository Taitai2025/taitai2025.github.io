import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Integrating an unbounded measurable transfer function

This file proves the invariant-average inequality directly by truncation and
Fatou's lemma. The transfer function is measurable, finite, and nonnegative;
it need not be integrable. No pointwise ergodic theorem or ergodic decomposition
is assumed. This provides an alternative verified route for the manuscript's
use of recurrence and Birkhoff averages on a fixed support.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace BB

/-- Upper truncation contracts an increment toward zero. -/
theorem truncated_increment_lower_bound (x y N : ℝ) :
    min (y - x) 0 ≤ min y N - min x N := by
  by_cases hxy : x ≤ y
  · rw [min_eq_right (sub_nonneg.mpr hxy)]
    exact sub_nonneg.mpr (min_le_min_right N hxy)
  · have hyx : y ≤ x := le_of_lt (lt_of_not_ge hxy)
    rw [min_eq_left (sub_nonpos.mpr hyx)]
    by_cases hxN : x ≤ N
    · rw [min_eq_left hxN, min_eq_left (hyx.trans hxN)]
    · have hNx : N ≤ x := le_of_lt (lt_of_not_ge hxN)
      rw [min_eq_right hNx]
      by_cases hyN : y ≤ N
      · rw [min_eq_left hyN]
        linarith
      · rw [min_eq_right (le_of_lt (lt_of_not_ge hyN))]
        linarith

variable {X : Type*} [MeasurableSpace X]

/-- Integral invariance for a measurable observable does not require the map
to be injective or a measurable embedding. -/
theorem invariant_integral_comp
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : AEStronglyMeasurable f μ) :
    (∫ x, f (T x) ∂μ) = ∫ x, f x ∂μ := by
  have hfmap : AEStronglyMeasurable f (Measure.map T μ) := by
    rwa [hT.map_eq]
  rw [← integral_map hT.measurable.aemeasurable hfmap, hT.map_eq]

/-- A monotone integrable observable is actually constant along the dynamics
almost everywhere under an invariant measure. This is the support-endpoint
persistence mechanism, and it does not require ergodicity. -/
theorem invariant_monotone_observable
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : Integrable f μ)
    (hmono : ∀ᵐ x ∂μ, f x ≤ f (T x)) :
    ∀ᵐ x ∂μ, f x = f (T x) := by
  have hfT : Integrable (fun x => f (T x)) μ :=
    (hT.integrable_comp hf.aestronglyMeasurable).mpr hf
  exact (integral_eq_iff_of_ae_le hf hfT hmono).mp
    (invariant_integral_comp μ T hT f hf.aestronglyMeasurable).symm

theorem invariant_antitone_observable
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (f : X → ℝ) (hf : Integrable f μ)
    (hmono : ∀ᵐ x ∂μ, f (T x) ≤ f x) :
    ∀ᵐ x ∂μ, f (T x) = f x := by
  have hfT : Integrable (fun x => f (T x)) μ :=
    (hT.integrable_comp hf.aestronglyMeasurable).mpr hf
  exact (integral_eq_iff_of_ae_le hfT hf hmono).mp
    (invariant_integral_comp μ T hT f hf.aestronglyMeasurable)

/-- A measurable forward-invariant event is invariant modulo null sets under
a finite invariant measure. Ergodicity is not required. -/
theorem invariant_event_of_forward_closed
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (A : Set X) (hA : MeasurableSet A)
    (hforward : A ⊆ T ⁻¹' A) : A =ᵐ[μ] T ⁻¹' A :=
  ae_eq_of_subset_of_measure_ge hforward (hT.measure_preimage hA).le
    hA (measure_ne_top μ _)

theorem invariant_event_of_preimage_subset
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (A : Set X) (hA : MeasurableSet A)
    (hbackward : T ⁻¹' A ⊆ A) : T ⁻¹' A =ᵐ[μ] A :=
  ae_eq_of_subset_of_measure_ge hbackward (hT.measure_preimage hA).symm.le
    (hA.preimage hT.measurable) (measure_ne_top μ _)

/-- An integrable function below a measurable finite coboundary has
nonpositive integral, even if the nonnegative transfer function is unbounded
and nonintegrable. -/
theorem integral_le_zero_of_le_coboundary
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (h : X → ℝ) (hh : Measurable h) (hnonneg : ∀ x, 0 ≤ h x)
    (f : X → ℝ) (hf : Integrable f μ)
    (hbound : ∀ᵐ x ∂μ, f x ≤ h (T x) - h x) :
    (∫ x, f x ∂μ) ≤ 0 := by
  let L : X → ℝ := fun x => min (f x) 0
  let q : X → ℝ := fun x => h (T x) - h x
  let H : ℕ → X → ℝ := fun n x => min (h x) (n : ℝ)
  let Q : ℕ → X → ℝ := fun n x => H n (T x) - H n x
  have hLmeas : AEStronglyMeasurable L μ :=
    (hf.aemeasurable.min aemeasurable_const).aestronglyMeasurable
  have hLint : Integrable L μ := by
    apply hf.mono hLmeas
    filter_upwards [] with x
    change ‖min (f x) 0‖ ≤ ‖f x‖
    by_cases hx : f x ≤ 0
    · rw [min_eq_left hx]
    · rw [min_eq_right (le_of_lt (lt_of_not_ge hx))]
      simp
  have hqmeas : Measurable q := (hh.comp hT.measurable).sub hh
  have hHmeas : ∀ n, Measurable (H n) := fun n => hh.min measurable_const
  have hHint : ∀ n, Integrable (H n) μ := by
    intro n
    apply (integrable_const (n : ℝ)).mono' (hHmeas n).aestronglyMeasurable
    filter_upwards [] with x
    change ‖min (h x) (n : ℝ)‖ ≤ (n : ℝ)
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnonneg x) (Nat.cast_nonneg n))]
    exact min_le_right _ _
  have hHintT : ∀ n, Integrable (fun x => H n (T x)) μ := by
    intro n
    exact (hT.integrable_comp (hHmeas n).aestronglyMeasurable).mpr (hHint n)
  have hQint : ∀ n, Integrable (Q n) μ := fun n => (hHintT n).sub (hHint n)
  have hQzero : ∀ n, (∫ x, Q n x ∂μ) = 0 := by
    intro n
    have hi : (∫ x, H n (T x) ∂μ) = ∫ x, H n x ∂μ := by
      rw [← integral_map hT.measurable.aemeasurable (hHmeas n).aestronglyMeasurable,
        hT.map_eq]
    change (∫ x, H n (T x) - H n x ∂μ) = 0
    rw [integral_sub (hHintT n) (hHint n), hi, sub_self]
  have hQL : ∀ n, ∀ᵐ x ∂μ, L x ≤ Q n x := by
    intro n
    filter_upwards [hbound] with x hx
    exact (min_le_min_right 0 hx).trans
      (truncated_increment_lower_bound (h x) (h (T x)) (n : ℝ))
  have hqL : ∀ᵐ x ∂μ, L x ≤ q x := by
    filter_upwards [hbound] with x hx
    exact (min_le_left _ _).trans hx
  have hQLnonneg : ∀ n, 0 ≤ᵐ[μ] (fun x => Q n x - L x) := by
    intro n
    filter_upwards [hQL n] with x hx
    exact sub_nonneg.mpr hx
  have hqLnonneg : 0 ≤ᵐ[μ] (fun x => q x - L x) := by
    filter_upwards [hqL] with x hx
    exact sub_nonneg.mpr hx
  have hnonposL : (∫ x, L x ∂μ) ≤ 0 :=
    integral_nonpos (fun x => min_le_right _ _)
  have hlim : ∀ x, Tendsto (fun n => ENNReal.ofReal (Q n x - L x)) atTop
      (𝓝 (ENNReal.ofReal (q x - L x))) := by
    intro x
    obtain ⟨N, hN⟩ := exists_nat_ge (max (h x) (h (T x)))
    have hevent : (fun n => ENNReal.ofReal (Q n x - L x)) =ᶠ[atTop]
        (fun _ => ENNReal.ofReal (q x - L x)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hNn : (N : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn
      have hx : h x ≤ (n : ℝ) := (le_max_left _ _).trans (hN.trans hNn)
      have hTx : h (T x) ≤ (n : ℝ) := (le_max_right _ _).trans (hN.trans hNn)
      simp only [Q, H, q, min_eq_left hx, min_eq_left hTx]
    exact (tendsto_congr' hevent).mpr tendsto_const_nhds
  have hENint : ∀ n, (∫⁻ x, ENNReal.ofReal (Q n x - L x) ∂μ) =
      ENNReal.ofReal (-(∫ x, L x ∂μ)) := by
    intro n
    calc
      (∫⁻ x, ENNReal.ofReal (Q n x - L x) ∂μ) =
          ENNReal.ofReal (∫ x, Q n x - L x ∂μ) := by
        simpa only [Pi.sub_apply] using
          (ofReal_integral_eq_lintegral_ofReal ((hQint n).sub hLint) (hQLnonneg n)).symm
      _ = ENNReal.ofReal (-(∫ x, L x ∂μ)) := by
        rw [integral_sub (hQint n) hLint, hQzero n, zero_sub]
  have hFatou : (∫⁻ x, ENNReal.ofReal (q x - L x) ∂μ) ≤
      ENNReal.ofReal (-(∫ x, L x ∂μ)) := by
    calc
      (∫⁻ x, ENNReal.ofReal (q x - L x) ∂μ) =
          ∫⁻ x, liminf (fun n => ENNReal.ofReal (Q n x - L x)) atTop ∂μ :=
        lintegral_congr (fun x => (hlim x).liminf_eq.symm)
      _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal (Q n x - L x) ∂μ) atTop :=
        lintegral_liminf_le' (fun n => ((hQint n).sub hLint).aemeasurable.ennreal_ofReal)
      _ = ENNReal.ofReal (-(∫ x, L x ∂μ)) := by
        simp only [hENint, liminf_const]
  have hqLint : Integrable (fun x => q x - L x) μ := by
    refine ⟨hqmeas.aestronglyMeasurable.sub hLmeas, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hqLnonneg).mpr
      (lt_of_le_of_lt hFatou ENNReal.ofReal_lt_top)
  have hqint : Integrable q μ := by
    convert hqLint.add hLint using 1
    ext x
    simp
  have hreal : (∫ x, q x - L x ∂μ) ≤ -(∫ x, L x ∂μ) := by
    rw [integral_eq_lintegral_of_nonneg_ae hqLnonneg hqLint.aestronglyMeasurable]
    simpa only [ENNReal.toReal_ofReal (neg_nonneg.mpr hnonposL)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hFatou
  rw [integral_sub hqint hLint] at hreal
  have hqnonpos : (∫ x, q x ∂μ) ≤ 0 := by linarith
  exact (integral_mono_ae hf hqint hbound).trans hqnonpos

/-- Invariant average bound for a nonnegative measurable transfer function.
The transfer function is intentionally not required to be integrable. -/
theorem coboundary_integral_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (h : X → ℝ) (hh : Measurable h) (hnonneg : ∀ x, 0 ≤ h x)
    (f : X → ℝ) (hf : Integrable f μ) (β : ℝ)
    (hbound : ∀ᵐ x ∂μ, f x ≤ β + h (T x) - h x) :
    (∫ x, f x ∂μ) ≤ β := by
  have hshift : ∀ᵐ x ∂μ, f x - β ≤ h (T x) - h x := by
    filter_upwards [hbound] with x hx
    linarith
  have hle := integral_le_zero_of_le_coboundary μ T hT h hh hnonneg
    (fun x => f x - β) (hf.sub (integrable_const β)) hshift
  rw [integral_sub hf (integrable_const β)] at hle
  simpa only [integral_const, measure_univ, ENNReal.one_toReal, one_smul,
    sub_nonpos] using hle

/-- Equality of the maximal invariant average forces a nonnegative measurable
defect to vanish almost everywhere. Only `min D 1` is integrated, so neither
the full defect nor the transfer function needs an integrability hypothesis. -/
theorem coboundary_defect_zero_of_maximal_integral
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (h : X → ℝ) (hh : Measurable h) (hnonneg : ∀ x, 0 ≤ h x)
    (f : X → ℝ) (hf : Integrable f μ) (β : ℝ)
    (D : X → ℝ) (hD : Measurable D) (hDnonneg : ∀ x, 0 ≤ D x)
    (hbound : ∀ᵐ x ∂μ, f x + D x ≤ β + h (T x) - h x)
    (hmaximal : (∫ x, f x ∂μ) = β) :
    ∀ᵐ x ∂μ, D x = 0 := by
  let d : X → ℝ := fun x => min (D x) 1
  have hdnonneg : ∀ x, 0 ≤ d x := fun x => le_min (hDnonneg x) zero_le_one
  have hdint : Integrable d μ := by
    apply (integrable_const (1 : ℝ)).mono' (hD.min measurable_const).aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hdnonneg x)]
    exact min_le_right _ _
  have hfd : ∀ᵐ x ∂μ, (f + d) x ≤ β + h (T x) - h x := by
    filter_upwards [hbound] with x hx
    have hd : d x ≤ D x := min_le_left _ _
    change f x + d x ≤ β + h (T x) - h x
    linarith
  have hle := coboundary_integral_bound μ T hT h hh hnonneg
    (f + d) (hf.add hdint) β hfd
  have hsum : (∫ x, (f + d) x ∂μ) = (∫ x, f x ∂μ) + (∫ x, d x ∂μ) :=
    integral_add hf hdint
  rw [hsum, hmaximal] at hle
  have hd0 : (∫ x, d x ∂μ) = 0 :=
    le_antisymm (by linarith) (integral_nonneg hdnonneg)
  have hae := (integral_eq_zero_iff_of_nonneg hdnonneg hdint).mp hd0
  filter_upwards [hae] with x hx
  change min (D x) 1 = 0 at hx
  by_cases hsmall : D x ≤ 1
  · simpa only [min_eq_left hsmall] using hx
  · have hone : (1 : ℝ) = 0 := by
      simpa only [min_eq_right (le_of_lt (lt_of_not_ge hsmall))] using hx
    norm_num at hone

end BB
