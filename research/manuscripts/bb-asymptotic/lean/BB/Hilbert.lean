import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Typeclasses
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Verified components of the Hilbert-space argument

This file proves measure reweighting, null-set/support persistence, the scalar
endpoint-band logarithmic transfer identity, and midpoint integral rigidity.
It does not assert the full operator spectral theorem, ergodic theorem,
semiuniform theorem, or the main Hilbert BB convergence theorem.

The extended-real normalization is an actual measure construction. The later
real logarithm lemmas have explicit strict positivity hypotheses; no singular
state is represented by `Real.log 0`.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal

namespace BB

variable {X : Type*} [MeasurableSpace X]

/-- Normalize the measure with nonnegative density `q`. The probability result
below separately requires its mass to be positive and finite. -/
def normalizedReweight (μ : Measure X) (q : X → ℝ≥0∞) : Measure X :=
  (∫⁻ x, q x ∂μ)⁻¹ • μ.withDensity q

theorem normalizedReweight_apply (μ : Measure X) (q : X → ℝ≥0∞)
    {B : Set X} (hB : MeasurableSet B) :
    normalizedReweight μ q B =
      (∫⁻ x, q x ∂μ)⁻¹ * ∫⁻ x in B, q x ∂μ := by
  simp [normalizedReweight, Measure.smul_apply, withDensity_apply q hB]

theorem normalizedReweight_probability (μ : Measure X) (q : X → ℝ≥0∞)
    (hzero : (∫⁻ x, q x ∂μ) ≠ 0)
    (hfinite : (∫⁻ x, q x ∂μ) ≠ ∞) :
    IsProbabilityMeasure (normalizedReweight μ q) := by
  constructor
  rw [normalizedReweight_apply μ q MeasurableSet.univ, Measure.restrict_univ]
  exact ENNReal.inv_mul_cancel hzero hfinite

theorem normalizedReweight_absolutelyContinuous
    (μ : Measure X) (q : X → ℝ≥0∞) :
    normalizedReweight μ q ≪ μ :=
  (withDensity_absolutelyContinuous μ q).smul _

theorem normalizedReweight_zero_of_zero (μ : Measure X) (q : X → ℝ≥0∞)
    {B : Set X} (hB : μ B = 0) : normalizedReweight μ q B = 0 :=
  normalizedReweight_absolutelyContinuous μ q hB

/-- For a positive almost-everywhere density and a finite normalizer, null
sets agree in both directions. This is used for fixed positive weights. -/
theorem normalizedReweight_zero_iff (μ : Measure X) (q : X → ℝ≥0∞)
    (hq : AEMeasurable q μ) (hpositive : ∀ᵐ x ∂μ, q x ≠ 0)
    (hfinite : (∫⁻ x, q x ∂μ) ≠ ∞) (B : Set X) :
    normalizedReweight μ q B = 0 ↔ μ B = 0 := by
  constructor
  · intro h
    apply withDensity_absolutelyContinuous' hq hpositive
    have hmul : (∫⁻ x, q x ∂μ)⁻¹ * μ.withDensity q B = 0 := by
      simpa [normalizedReweight, Measure.smul_apply] using h
    exact (mul_eq_zero.mp hmul).resolve_left (ENNReal.inv_ne_zero.mpr hfinite)
  · exact normalizedReweight_zero_of_zero μ q

/-- The usual neighborhood definition of the topological support of a measure.
It avoids imposing separability or regularity merely for support monotonicity. -/
def measureSupport [TopologicalSpace X] (μ : Measure X) : Set X :=
  {x | ∀ U : Set X, IsOpen U → x ∈ U → μ U ≠ 0}

theorem measureSupport_subset_of_absolutelyContinuous [TopologicalSpace X]
    {μ ν : Measure X} (h : ν ≪ μ) : measureSupport ν ⊆ measureSupport μ := by
  intro x hx U hU hxU hzero
  exact hx U hU hxU (h hzero)

theorem normalizedReweight_support_subset [TopologicalSpace X]
    (μ : Measure X) (q : X → ℝ≥0∞) :
    measureSupport (normalizedReweight μ q) ⊆ measureSupport μ :=
  measureSupport_subset_of_absolutelyContinuous
    (normalizedReweight_absolutelyContinuous μ q)

theorem normalizedReweight_support_eq [TopologicalSpace X]
    (μ : Measure X) (q : X → ℝ≥0∞)
    (hq : AEMeasurable q μ) (hpositive : ∀ᵐ x ∂μ, q x ≠ 0)
    (hfinite : (∫⁻ x, q x ∂μ) ≠ ∞) :
    measureSupport (normalizedReweight μ q) = measureSupport μ := by
  ext x
  constructor
  · exact fun hx => normalizedReweight_support_subset μ q hx
  · intro hx U hU hxU hzero
    exact hx U hU hxU ((normalizedReweight_zero_iff μ q hq hpositive hfinite U).mp hzero)

/-- Null spectral sets remain null through every iterate of a sequence of
absolutely continuous updates. No common fixed density is assumed. -/
theorem zero_mass_persists (μ : ℕ → Measure X)
    (hstep : ∀ n, μ (n + 1) ≪ μ n) {B : Set X} (hB : μ 0 B = 0) :
    ∀ n, μ n B = 0 := by
  intro n
  induction n with
  | zero => exact hB
  | succ n ih => exact hstep n ih

/-- The actual Hilbert spectral-measure update at a prescribed reciprocal step. -/
def spectralMeasureStep (ν : Measure ℝ) (u : ℝ) : Measure ℝ :=
  normalizedReweight ν (fun x => ENNReal.ofReal ((1 - x / u) ^ 2))

theorem spectralMeasureStep_support_subset (ν : Measure ℝ) (u : ℝ) :
    measureSupport (spectralMeasureStep ν u) ⊆ measureSupport ν :=
  normalizedReweight_support_subset ν _

theorem spectralMeasureStep_probability (ν : Measure ℝ) (u : ℝ)
    (hint : Integrable (fun x : ℝ => (1 - x / u) ^ 2) ν)
    (hreg : 0 < ∫ x : ℝ, (1 - x / u) ^ 2 ∂ν) :
    IsProbabilityMeasure (spectralMeasureStep ν u) := by
  have hmass : (∫⁻ x : ℝ, ENNReal.ofReal ((1 - x / u) ^ 2) ∂ν) =
      ENNReal.ofReal (∫ x : ℝ, (1 - x / u) ^ 2 ∂ν) :=
    (ofReal_integral_eq_lintegral_ofReal hint
      (eventually_of_forall fun x => sq_nonneg (1 - x / u))).symm
  apply normalizedReweight_probability
  · rw [hmass]
    exact (ENNReal.ofReal_pos.mpr hreg).ne'
  · rw [hmass]
    exact ENNReal.ofReal_ne_top

/-- Weighted logarithmic potential of two strictly positive band masses. -/
def bandPotential (p q l u : ℝ) : ℝ :=
  -(p / 2) * Real.log l - (q / 2) * Real.log u

/-- Exact scalar identity underlying the endpoint-band certificate. `L,Q` are
the two band averages of the squared multiplier, and `R` is its full average. -/
theorem band_transfer_identity (p q l u L U R : ℝ)
    (hpq : p + q = 1) (hl : 0 < l) (hu : 0 < u)
    (hL : 0 < L) (hU : 0 < U) (hR : 0 < R) :
    bandPotential p q (l * L / R) (u * U / R) - bandPotential p q l u =
      Real.log R / 2 - p / 2 * Real.log L - q / 2 * Real.log U := by
  have hq : q = 1 - p := by linarith
  simp only [bandPotential, Real.log_div (mul_pos hl hL).ne' hR.ne',
    Real.log_div (mul_pos hu hU).ne' hR.ne',
    Real.log_mul hl.ne' hL.ne', Real.log_mul hu.ne' hU.ne']
  rw [hq]
  ring

/-- The algebraic band certificate with explicit upper bounds on both
conditional squared-multiplier averages. -/
theorem band_transfer_bound (p q l u L U R s t : ℝ)
    (hpq : p + q = 1) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hl : 0 < l) (hu : 0 < u) (hL : 0 < L) (hU : 0 < U) (hR : 0 < R)
    (_hs : 0 < s) (_ht : 0 < t) (hLs : L ≤ s ^ 2) (hUt : U ≤ t ^ 2) :
    Real.log R / 2 ≤ p * Real.log s + q * Real.log t +
      bandPotential p q (l * L / R) (u * U / R) - bandPotential p q l u := by
  have hlogL : Real.log L ≤ 2 * Real.log s := by
    calc
      Real.log L ≤ Real.log (s ^ 2) := Real.log_le_log hL hLs
      _ = 2 * Real.log s := by rw [Real.log_pow]; norm_num
  have hlogU : Real.log U ≤ 2 * Real.log t := by
    calc
      Real.log U ≤ Real.log (t ^ 2) := Real.log_le_log hU hUt
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have hpL := mul_le_mul_of_nonneg_left hlogL hp
  have hqU := mul_le_mul_of_nonneg_left hlogU hq
  have hid := band_transfer_identity p q l u L U R hpq hl hu hL hU hR
  linarith

/-! ## Midpoint squared-multiplier rigidity -/

theorem midpoint_gap_identity (a b x : ℝ) (hsum : a + b ≠ 0) :
    ((b - a) / (a + b)) ^ 2 - (1 - 2 * x / (a + b)) ^ 2 =
      4 * (x - a) * (b - x) / (a + b) ^ 2 := by
  field_simp
  ring

theorem midpoint_multiplier_le (a b x : ℝ) (ha : 0 < a) (hab : a < b)
    (hxa : a ≤ x) (hxb : x ≤ b) :
    (1 - 2 * x / (a + b)) ^ 2 ≤ ((b - a) / (a + b)) ^ 2 := by
  have hsum : a + b ≠ 0 := ne_of_gt (by linarith)
  have hgap := midpoint_gap_identity a b x hsum
  have hnonneg : 0 ≤ 4 * (x - a) * (b - x) / (a + b) ^ 2 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hxa))
      (sub_nonneg.mpr hxb)) (sq_nonneg _)
  linarith

theorem midpoint_multiplier_eq_iff (a b x : ℝ) (ha : 0 < a) (hab : a < b) :
    (1 - 2 * x / (a + b)) ^ 2 = ((b - a) / (a + b)) ^ 2 ↔
      x = a ∨ x = b := by
  have hsum : a + b ≠ 0 := ne_of_gt (by linarith)
  have hgap := midpoint_gap_identity a b x hsum
  constructor
  · intro heq
    have hprod : (x - a) * (b - x) = 0 := by
      have : 4 * (x - a) * (b - x) = 0 := by
        apply (div_eq_zero_iff.mp ?_).resolve_right (pow_ne_zero 2 hsum)
        linarith
      nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h).symm
  · rintro (rfl | rfl) <;> field_simp <;> ring

/-- If the midpoint squared multiplier attains its largest possible integral,
all spectral mass is concentrated at the two endpoints. This is an actual
probability-measure rigidity result, not an assumption of endpoint support. -/
theorem midpoint_integral_rigidity_of_integrable (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, x ∈ Set.Icc a b)
    (hint : Integrable (fun x : ℝ => (1 - 2 * x / (a + b)) ^ 2) ν)
    (heq : (∫ x : ℝ, (1 - 2 * x / (a + b)) ^ 2 ∂ν) =
      ((b - a) / (a + b)) ^ 2) :
    ∀ᵐ x ∂ν, x = a ∨ x = b := by
  have hle : (fun x : ℝ => (1 - 2 * x / (a + b)) ^ 2) ≤ᵐ[ν]
      (fun _ => ((b - a) / (a + b)) ^ 2) := by
    filter_upwards [hsupport] with x hx
    exact midpoint_multiplier_le a b x ha hab hx.1 hx.2
  have hconst : (∫ _ : ℝ, ((b - a) / (a + b)) ^ 2 ∂ν) =
      ((b - a) / (a + b)) ^ 2 := by simp
  have hae := (integral_eq_iff_of_ae_le hint
    (integrable_const (((b - a) / (a + b)) ^ 2)) hle).mp (heq.trans hconst.symm)
  filter_upwards [hae] with x hx
  exact (midpoint_multiplier_eq_iff a b x ha hab).mp hx

theorem midpoint_multiplier_integrable (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) :
    Integrable (fun x : ℝ => (1 - 2 * x / (a + b)) ^ 2) ν := by
  have hc : Continuous (fun x : ℝ => (1 - 2 * x / (a + b)) ^ 2) :=
    (continuous_const.sub ((continuous_const.mul continuous_id).div_const _)).pow 2
  apply (integrable_const (((b - a) / (a + b)) ^ 2)).mono' hc.aestronglyMeasurable
  filter_upwards [hsupport] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact midpoint_multiplier_le a b x ha hab hx.1 hx.2

/-- The full midpoint integral-rigidity statement needs no extra integrability
hypothesis: compact spectral bounds supply it. -/
theorem midpoint_integral_rigidity (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, x ∈ Set.Icc a b)
    (heq : (∫ x : ℝ, (1 - 2 * x / (a + b)) ^ 2 ∂ν) =
      ((b - a) / (a + b)) ^ 2) :
    ∀ᵐ x ∂ν, x = a ∨ x = b :=
  midpoint_integral_rigidity_of_integrable a b ha hab ν hsupport
    (midpoint_multiplier_integrable a b ha hab ν hsupport) heq

theorem spectral_coordinate_integrable (a b : ℝ) (ha : 0 < a)
    (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) : Integrable (fun x : ℝ => x) ν := by
  apply (integrable_const b).mono' measurable_id.aestronglyMeasurable
  filter_upwards [hsupport] with x hx
  change ‖x‖ ≤ b
  rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le ha hx.1)]
  exact hx.2

/-- If both distinct positive endpoints belong to the support, the spectral
mean lies strictly between them, also for non-atomic spectral measures. -/
theorem spectral_mean_interior (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hsupport : ∀ᵐ x ∂ν, x ∈ Set.Icc a b)
    (haSupport : a ∈ measureSupport ν) (hbSupport : b ∈ measureSupport ν) :
    a < (∫ x : ℝ, x ∂ν) ∧ (∫ x : ℝ, x ∂ν) < b := by
  have hint := spectral_coordinate_integrable a b ha ν hsupport
  have hleft_nonneg : 0 ≤ᵐ[ν] (fun x : ℝ => x - a) := by
    filter_upwards [hsupport] with x hx
    exact sub_nonneg.mpr hx.1
  have hleft_mass : 0 < ν (Function.support (fun x : ℝ => x - a)) := by
    have hpos : 0 < ν (Ioi a) := pos_iff_ne_zero.mpr
      (hbSupport (Ioi a) isOpen_Ioi hab)
    apply lt_of_lt_of_le hpos (measure_mono ?_)
    intro x hx
    change x - a ≠ 0
    exact (sub_pos.mpr (show a < x from hx)).ne'
  have hleft : 0 < ∫ x : ℝ, x - a ∂ν :=
    (integral_pos_iff_support_of_nonneg_ae hleft_nonneg
      (hint.sub (integrable_const a))).mpr hleft_mass
  have hright_nonneg : 0 ≤ᵐ[ν] (fun x : ℝ => b - x) := by
    filter_upwards [hsupport] with x hx
    exact sub_nonneg.mpr hx.2
  have hright_mass : 0 < ν (Function.support (fun x : ℝ => b - x)) := by
    have hpos : 0 < ν (Iio b) := pos_iff_ne_zero.mpr
      (haSupport (Iio b) isOpen_Iio hab)
    apply lt_of_lt_of_le hpos (measure_mono ?_)
    intro x hx
    change b - x ≠ 0
    exact (sub_pos.mpr (show x < b from hx)).ne'
  have hright : 0 < ∫ x : ℝ, b - x ∂ν :=
    (integral_pos_iff_support_of_nonneg_ae hright_nonneg
      ((integrable_const b).sub hint)).mpr hright_mass
  rw [integral_sub hint (integrable_const a)] at hleft
  rw [integral_sub (integrable_const b) hint] at hright
  simp only [integral_const, measure_univ, ENNReal.one_toReal, one_smul] at hleft hright
  exact ⟨sub_pos.mp hleft, sub_pos.mp hright⟩

end BB
