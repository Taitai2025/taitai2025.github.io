import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Algebra.GeomSum
import Mathlib.Tactic

/-!
# Local BB secant estimates

These results formalize the Hilbert-space secant estimates used in Section 6.
The two-point remainder estimate and the linear model's bounds are explicit
hypotheses. No nonlinear localization or spectral theorem is assumed here.
-/

noncomputable section

namespace BB.Nonlinear

open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The long BB quotient. Its legitimate evaluation domain is proved below. -/
def bb1 (s v : E) : ℝ := ‖s‖ ^ 2 / inner (𝕜 := ℝ) s v

/-- The short BB quotient. Its legitimate evaluation domain is proved below. -/
def bb2 (s v : E) : ℝ := inner (𝕜 := ℝ) s v / ‖v‖ ^ 2

/-- A relative vector remainder controls the corresponding inner product. -/
theorem inner_remainder_bound (s v w : E) (ε : ℝ)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    |inner (𝕜 := ℝ) s v - inner (𝕜 := ℝ) s w| ≤ ε * ‖s‖ ^ 2 := by
  calc
    |inner (𝕜 := ℝ) s v - inner (𝕜 := ℝ) s w|
        = |inner (𝕜 := ℝ) s (v - w)| := by rw [inner_sub_right]
    _ ≤ ‖s‖ * ‖v - w‖ := abs_real_inner_le_norm s (v - w)
    _ ≤ ‖s‖ * (ε * ‖s‖) := mul_le_mul_of_nonneg_left hrem (norm_nonneg s)
    _ = ε * ‖s‖ ^ 2 := by ring

/-- Equation (6.13): two-sided monotonicity of a perturbed secant. -/
theorem secant_inner_bounds (s v w : E) (m M ε : ℝ)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hhi : inner (𝕜 := ℝ) s w ≤ M * ‖s‖ ^ 2)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    (m - ε) * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s v ∧
      inner (𝕜 := ℝ) s v ≤ (M + ε) * ‖s‖ ^ 2 := by
  have h := abs_le.mp (inner_remainder_bound s v w ε hrem)
  constructor <;> nlinarith only [hlo, hhi, h.1, h.2]

/-- Equation (6.14): norm bounds for a secant, derived from its relative error. -/
theorem secant_norm_bounds (s v w : E) (m M ε : ℝ) (hs : s ≠ 0)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hhi : inner (𝕜 := ℝ) s w ≤ M * ‖s‖ ^ 2)
    (hw : ‖w‖ ≤ M * ‖s‖)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    (m - ε) * ‖s‖ ≤ ‖v‖ ∧ ‖v‖ ≤ (M + ε) * ‖s‖ := by
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hi := (secant_inner_bounds s v w m M ε hlo hhi hrem).1
  constructor
  · apply le_of_mul_le_mul_left (a := ‖s‖) _ hspos
    calc
      ‖s‖ * ((m - ε) * ‖s‖) = (m - ε) * ‖s‖ ^ 2 := by ring
      _ ≤ inner (𝕜 := ℝ) s v := hi
      _ ≤ ‖s‖ * ‖v‖ := real_inner_le_norm s v
  · calc
      ‖v‖ = ‖(v - w) + w‖ := by congr 1; abel
      _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ε * ‖s‖ + M * ‖s‖ := add_le_add hrem hw
      _ = (M + ε) * ‖s‖ := by ring

/-- Positivity and both compact BB1/BB2 step intervals.

This is the step-size part of `lem:local-secant-geometry` in the manuscript.
The vector `w` is the frozen model `A s`; all model bounds are shown explicitly.
-/
theorem bb_step_bounds (s v w : E) (m M ε : ℝ) (hs : s ≠ 0)
    (hm : 0 < m) (hmM : m ≤ M) (hε : 0 ≤ ε) (hεm : ε < m)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hhi : inner (𝕜 := ℝ) s w ≤ M * ‖s‖ ^ 2)
    (hw : ‖w‖ ≤ M * ‖s‖)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    0 < inner (𝕜 := ℝ) s v ∧ 0 < ‖v‖ ∧
    0 < bb1 s v ∧ 0 < bb2 s v ∧
    1 / (M + ε) ≤ bb1 s v ∧ bb1 s v ≤ 1 / (m - ε) ∧
    (m - ε) / (M + ε) ^ 2 ≤ bb2 s v ∧ bb2 s v ≤ 1 / (m - ε) := by
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hs2 : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hspos
  have hminus : 0 < m - ε := sub_pos.mpr hεm
  have hplus : 0 < M + ε := by linarith
  have hi := secant_inner_bounds s v w m M ε hlo hhi hrem
  have hn := secant_norm_bounds s v w m M ε hs hlo hhi hw hrem
  have hp : 0 < inner (𝕜 := ℝ) s v := (mul_pos hminus hs2).trans_le hi.1
  have hv : 0 < ‖v‖ := (mul_pos hminus hspos).trans_le hn.1
  have hv2 : 0 < ‖v‖ ^ 2 := sq_pos_of_pos hv
  have hplus2 : 0 < (M + ε) ^ 2 := sq_pos_of_pos hplus
  refine ⟨hp, hv, div_pos hs2 hp, div_pos hp hv2, ?_, ?_, ?_, ?_⟩
  · change 1 / (M + ε) ≤ ‖s‖ ^ 2 / inner (𝕜 := ℝ) s v
    apply (div_le_div_iff hplus hp).mpr
    nlinarith only [hi.2]
  · change ‖s‖ ^ 2 / inner (𝕜 := ℝ) s v ≤ 1 / (m - ε)
    apply (div_le_div_iff hp hminus).mpr
    nlinarith only [hi.1]
  · change (m - ε) / (M + ε) ^ 2 ≤ inner (𝕜 := ℝ) s v / ‖v‖ ^ 2
    apply (div_le_div_iff hplus2 hv2).mpr
    have hsq : ‖v‖ ^ 2 ≤ (M + ε) ^ 2 * ‖s‖ ^ 2 := by
      have hprod := mul_self_le_mul_self (norm_nonneg v) hn.2
      nlinarith only [hprod]
    calc
      (m - ε) * ‖v‖ ^ 2 ≤ (m - ε) * ((M + ε) ^ 2 * ‖s‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq hminus.le
      _ = ((m - ε) * ‖s‖ ^ 2) * (M + ε) ^ 2 := by ring
      _ ≤ inner (𝕜 := ℝ) s v * (M + ε) ^ 2 :=
        mul_le_mul_of_nonneg_right hi.1 (sq_nonneg _)
  · change inner (𝕜 := ℝ) s v / ‖v‖ ^ 2 ≤ 1 / (m - ε)
    apply (div_le_div_iff hv2 hminus).mpr
    calc
      inner (𝕜 := ℝ) s v * (m - ε) ≤ (‖s‖ * ‖v‖) * (m - ε) :=
        mul_le_mul_of_nonneg_right (real_inner_le_norm s v) hminus.le
      _ = ((m - ε) * ‖s‖) * ‖v‖ := by ring
      _ ≤ ‖v‖ * ‖v‖ := mul_le_mul_of_nonneg_right hn.1 (norm_nonneg v)
      _ = 1 * ‖v‖ ^ 2 := by ring

/-- Scalar reciprocal perturbation bound used for BB1. -/
theorem reciprocal_perturbation (a b m ε : ℝ) (hm : 0 < m)
    (hε : 0 ≤ ε) (hεm : ε ≤ m / 2) (ha : m ≤ a) (hd : |b - a| ≤ ε) :
    |1 / b - 1 / a| ≤ 2 * ε / m ^ 2 := by
  have habs := abs_le.mp hd
  have ha0 : 0 < a := hm.trans_le ha
  have hbhalf : m / 2 ≤ b := by linarith [habs.1]
  have hb0 : 0 < b := by linarith
  have hprod : 0 < a * b := mul_pos ha0 hb0
  have hm2 : 0 < m ^ 2 / 2 := by positivity
  have hprodlo : m ^ 2 / 2 ≤ a * b := by
    have hp := mul_le_mul ha hbhalf (by positivity : 0 ≤ m / 2) ha0.le
    nlinarith only [hp]
  have hid : 1 / b - 1 / a = (a - b) / (a * b) := by
    field_simp [ha0.ne', hb0.ne']
    ring_nf
    simp
  calc
    |1 / b - 1 / a| = |a - b| / (a * b) := by
      rw [hid, abs_div, abs_of_pos hprod]
    _ ≤ ε / (a * b) := div_le_div_of_nonneg_right (by simpa [abs_sub_comm] using hd) hprod.le
    _ ≤ ε / (m ^ 2 / 2) := div_le_div_of_nonneg_left hε hm2 hprodlo
    _ = 2 * ε / m ^ 2 := by ring

/-- The explicit scalar BB2 perturbation estimate, with every denominator bound
recorded.  In the Hilbert-space application all four variables are normalized
by the squared secant norm. -/
theorem quotient_perturbation (a q d h m M ε : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hε : 0 ≤ ε) (hεm : ε ≤ m / 2)
    (ha : |a| ≤ M) (hqlo : m ^ 2 ≤ q) (hqhi : q ≤ M ^ 2)
    (hd : |d| ≤ ε) (hh : |h| ≤ 2 * M * ε + ε ^ 2)
    (hb : (m - ε) ^ 2 ≤ q + h) :
    |(a + d) / (q + h) - a / q| ≤ 14 * M ^ 2 * ε / m ^ 4 := by
  have hM : 0 < M := hm.trans_le hmM
  have hq : 0 < q := (sq_pos_of_pos hm).trans_le hqlo
  have hminus : 0 < m - ε := by linarith
  have hden : 0 < q + h := (sq_pos_of_pos hminus).trans_le hb
  have heM : ε ≤ M / 2 := by linarith
  have hnum0 : 0 ≤ 7 / 2 * M ^ 2 * ε := by positivity
  have hnum : |q * d - a * h| ≤ 7 / 2 * M ^ 2 * ε := by
    calc
      |q * d - a * h| ≤ |q * d| + |a * h| := abs_sub _ _
      _ = q * |d| + |a| * |h| := by rw [abs_mul, abs_mul, abs_of_pos hq]
      _ ≤ M ^ 2 * ε + M * (2 * M * ε + ε ^ 2) := by
        exact add_le_add (mul_le_mul hqhi hd (abs_nonneg d) (sq_nonneg M))
          (mul_le_mul ha hh (abs_nonneg h) hM.le)
      _ ≤ 7 / 2 * M ^ 2 * ε := by
        have hx := mul_le_mul_of_nonneg_left heM (mul_nonneg hM.le hε)
        nlinarith only [hx]
  have hsmall : m ^ 2 / 4 ≤ (m - ε) ^ 2 := by
    have hhalf : 0 ≤ m - ε - m / 2 := by linarith
    have hx := mul_nonneg hhalf (by linarith : 0 ≤ m - ε + m / 2)
    nlinarith only [hx]
  have hbottom : m ^ 4 / 4 ≤ q * (q + h) := by
    have hx := mul_le_mul hqlo (hsmall.trans hb) (by positivity : 0 ≤ m ^ 2 / 4) hq.le
    nlinarith only [hx]
  have hid : (a + d) / (q + h) - a / q = (q * d - a * h) / (q * (q + h)) := by
    field_simp [hq.ne', hden.ne']
    ring
  calc
    |(a + d) / (q + h) - a / q|
        = |q * d - a * h| / (q * (q + h)) := by
          rw [hid, abs_div, abs_of_pos (mul_pos hq hden)]
    _ ≤ (7 / 2 * M ^ 2 * ε) / (m ^ 4 / 4) :=
      div_le_div hnum0 hnum (by positivity) hbottom
    _ = 14 * M ^ 2 * ε / m ^ 4 := by ring

/-- Long-BB perturbation, specialized to actual Hilbert-space secants. -/
theorem bb1_perturbation (s v w : E) (m ε : ℝ) (hs : s ≠ 0)
    (hm : 0 < m) (hε : 0 ≤ ε) (hεm : ε ≤ m / 2)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    |bb1 s v - bb1 s w| ≤ 2 * ε / m ^ 2 := by
  have hS : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs)
  have ha : m ≤ inner (𝕜 := ℝ) s w / ‖s‖ ^ 2 := (le_div_iff hS).mpr hlo
  have hd : |inner (𝕜 := ℝ) s v / ‖s‖ ^ 2 -
      inner (𝕜 := ℝ) s w / ‖s‖ ^ 2| ≤ ε := by
    rw [← sub_div, abs_div, abs_of_pos hS]
    exact (div_le_iff hS).mpr (inner_remainder_bound s v w ε hrem)
  have h := reciprocal_perturbation
    (inner (𝕜 := ℝ) s w / ‖s‖ ^ 2)
    (inner (𝕜 := ℝ) s v / ‖s‖ ^ 2) m ε hm hε hεm ha hd
  simpa only [bb1, one_div_div] using h

/-- An inner-product coercivity estimate implies a vector-norm lower bound. -/
theorem norm_lower_of_inner_lower (s w : E) (m : ℝ) (hs : s ≠ 0)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w) :
    m * ‖s‖ ≤ ‖w‖ := by
  apply le_of_mul_le_mul_left (a := ‖s‖) _ (norm_pos_iff.mpr hs)
  calc
    ‖s‖ * (m * ‖s‖) = m * ‖s‖ ^ 2 := by ring
    _ ≤ inner (𝕜 := ℝ) s w := hlo
    _ ≤ ‖s‖ * ‖w‖ := real_inner_le_norm s w

/-- The relative error also controls the squared-norm denominator of BB2. -/
theorem squared_norm_remainder (s v w : E) (M ε : ℝ)
    (hM : 0 ≤ M) (_hε : 0 ≤ ε)
    (hw : ‖w‖ ≤ M * ‖s‖) (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    |‖v‖ ^ 2 - ‖w‖ ^ 2| ≤ (2 * M * ε + ε ^ 2) * ‖s‖ ^ 2 := by
  have hd2 : ‖v - w‖ ^ 2 ≤ ε ^ 2 * ‖s‖ ^ 2 := by
    have h := mul_self_le_mul_self (norm_nonneg (v - w)) hrem
    nlinarith only [h]
  have hi : |inner (𝕜 := ℝ) w (v - w)| ≤ M * ε * ‖s‖ ^ 2 := by
    calc
      |inner (𝕜 := ℝ) w (v - w)| ≤ ‖w‖ * ‖v - w‖ := abs_real_inner_le_norm _ _
      _ ≤ (M * ‖s‖) * (ε * ‖s‖) :=
        mul_le_mul hw hrem (norm_nonneg _) (mul_nonneg hM (norm_nonneg s))
      _ = M * ε * ‖s‖ ^ 2 := by ring
  have hid : ‖v‖ ^ 2 - ‖w‖ ^ 2 =
      2 * inner (𝕜 := ℝ) w (v - w) + ‖v - w‖ ^ 2 := by
    have h := norm_add_sq_real w (v - w)
    have heq : w + (v - w) = v := by abel
    rw [heq] at h
    linarith
  rw [hid]
  calc
    |2 * inner (𝕜 := ℝ) w (v - w) + ‖v - w‖ ^ 2|
        ≤ |2 * inner (𝕜 := ℝ) w (v - w)| + |‖v - w‖ ^ 2| := abs_add _ _
    _ = 2 * |inner (𝕜 := ℝ) w (v - w)| + ‖v - w‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg ‖v - w‖)]
      norm_num
    _ ≤ (2 * M * ε + ε ^ 2) * ‖s‖ ^ 2 := by nlinarith only [hi, hd2]

/-- Short-BB perturbation for Hilbert-space secants, including the constant 14. -/
theorem bb2_perturbation (s v w : E) (m M ε : ℝ) (hs : s ≠ 0)
    (hm : 0 < m) (hmM : m ≤ M) (hε : 0 ≤ ε) (hεm : ε ≤ m / 2)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hw : ‖w‖ ≤ M * ‖s‖)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    |bb2 s v - bb2 s w| ≤ 14 * M ^ 2 * ε / m ^ 4 := by
  have hspos : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hS : 0 < ‖s‖ ^ 2 := sq_pos_of_pos hspos
  have hM : 0 < M := hm.trans_le hmM
  have hminus : 0 < m - ε := by linarith
  have hwlo : m * ‖s‖ ≤ ‖w‖ := norm_lower_of_inner_lower s w m hs hlo
  have hsw : |inner (𝕜 := ℝ) s w| ≤ M * ‖s‖ ^ 2 := by
    calc
      |inner (𝕜 := ℝ) s w| ≤ ‖s‖ * ‖w‖ := abs_real_inner_le_norm s w
      _ ≤ ‖s‖ * (M * ‖s‖) := mul_le_mul_of_nonneg_left hw (norm_nonneg s)
      _ = M * ‖s‖ ^ 2 := by ring
  have hhi : inner (𝕜 := ℝ) s w ≤ M * ‖s‖ ^ 2 := (le_abs_self _).trans hsw
  have hvlo := (secant_norm_bounds s v w m M ε hs hlo hhi hw hrem).1
  have ha : |inner (𝕜 := ℝ) s w / ‖s‖ ^ 2| ≤ M := by
    rw [abs_div, abs_of_pos hS]
    exact (div_le_iff hS).mpr hsw
  have hqlo : m ^ 2 ≤ ‖w‖ ^ 2 / ‖s‖ ^ 2 := by
    apply (le_div_iff hS).mpr
    have h := mul_self_le_mul_self (mul_nonneg hm.le (norm_nonneg s)) hwlo
    nlinarith only [h]
  have hqhi : ‖w‖ ^ 2 / ‖s‖ ^ 2 ≤ M ^ 2 := by
    apply (div_le_iff hS).mpr
    have h := mul_self_le_mul_self (norm_nonneg w) hw
    nlinarith only [h]
  have hd : |inner (𝕜 := ℝ) s (v - w) / ‖s‖ ^ 2| ≤ ε := by
    rw [abs_div, abs_of_pos hS]
    apply (div_le_iff hS).mpr
    simpa only [inner_sub_right] using inner_remainder_bound s v w ε hrem
  have hh : |(‖v‖ ^ 2 - ‖w‖ ^ 2) / ‖s‖ ^ 2| ≤ 2 * M * ε + ε ^ 2 := by
    rw [abs_div, abs_of_pos hS]
    exact (div_le_iff hS).mpr (squared_norm_remainder s v w M ε hM.le hε hw hrem)
  have hqadd : ‖w‖ ^ 2 / ‖s‖ ^ 2 + (‖v‖ ^ 2 - ‖w‖ ^ 2) / ‖s‖ ^ 2 =
      ‖v‖ ^ 2 / ‖s‖ ^ 2 := by ring
  have hb : (m - ε) ^ 2 ≤ ‖w‖ ^ 2 / ‖s‖ ^ 2 +
      (‖v‖ ^ 2 - ‖w‖ ^ 2) / ‖s‖ ^ 2 := by
    rw [hqadd]
    apply (le_div_iff hS).mpr
    have h := mul_self_le_mul_self (mul_nonneg hminus.le (norm_nonneg s)) hvlo
    nlinarith only [h]
  have hpadd : inner (𝕜 := ℝ) s w / ‖s‖ ^ 2 + inner (𝕜 := ℝ) s (v - w) / ‖s‖ ^ 2 =
      inner (𝕜 := ℝ) s v / ‖s‖ ^ 2 := by rw [inner_sub_right]; ring
  have h := quotient_perturbation (inner (𝕜 := ℝ) s w / ‖s‖ ^ 2)
    (‖w‖ ^ 2 / ‖s‖ ^ 2) (inner (𝕜 := ℝ) s (v - w) / ‖s‖ ^ 2)
    ((‖v‖ ^ 2 - ‖w‖ ^ 2) / ‖s‖ ^ 2) m M ε hm hmM hε hεm ha hqlo hqhi hd hh hb
  rw [hpadd, hqadd, div_div_div_cancel_right _ hS.ne', div_div_div_cancel_right _ hS.ne'] at h
  exact h

/-- Both secant perturbations use the manuscript's common explicit constant. -/
theorem common_secant_perturbation (s v w : E) (m M ε : ℝ) (hs : s ≠ 0)
    (hm : 0 < m) (hmM : m ≤ M) (hε : 0 ≤ ε) (hεm : ε ≤ m / 2)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hw : ‖w‖ ≤ M * ‖s‖)
    (hrem : ‖v - w‖ ≤ ε * ‖s‖) :
    |bb1 s v - bb1 s w| ≤ max (2 / m ^ 2) (14 * M ^ 2 / m ^ 4) * ε ∧
    |bb2 s v - bb2 s w| ≤ max (2 / m ^ 2) (14 * M ^ 2 / m ^ 4) * ε := by
  constructor
  · calc
      |bb1 s v - bb1 s w| ≤ 2 * ε / m ^ 2 := bb1_perturbation s v w m ε hs hm hε hεm hlo hrem
      _ = (2 / m ^ 2) * ε := by ring
      _ ≤ max (2 / m ^ 2) (14 * M ^ 2 / m ^ 4) * ε :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hε
  · calc
      |bb2 s v - bb2 s w| ≤ 14 * M ^ 2 * ε / m ^ 4 :=
        bb2_perturbation s v w m M ε hs hm hmM hε hεm hlo hw hrem
      _ = (14 * M ^ 2 / m ^ 4) * ε := by ring
      _ ≤ max (2 / m ^ 2) (14 * M ^ 2 / m ^ 4) * ε :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hε

/-- Uniform reciprocal Lipschitz estimate on the positive half-line [m,∞). -/
theorem inverse_lipschitz (a b m D : ℝ) (hm : 0 < m)
    (ha : m ≤ a) (hb : m ≤ b) (hd : |a - b| ≤ D) :
    |1 / a - 1 / b| ≤ D / m ^ 2 := by
  have ha0 : 0 < a := hm.trans_le ha
  have hb0 : 0 < b := hm.trans_le hb
  have hD : 0 ≤ D := (abs_nonneg _).trans hd
  have hp : m ^ 2 ≤ a * b := by
    have h := mul_le_mul ha hb hm.le ha0.le
    nlinarith only [h]
  have hid : 1 / a - 1 / b = (b - a) / (a * b) := by
    field_simp [ha0.ne', hb0.ne']
  calc
    |1 / a - 1 / b| = |b - a| / (a * b) := by
      rw [hid, abs_div, abs_of_pos (mul_pos ha0 hb0)]
    _ ≤ D / m ^ 2 := div_le_div hD (by simpa [abs_sub_comm] using hd)
      (sq_pos_of_pos hm) hp

/-- Quadratic-form variation on the unit sphere. -/
theorem unit_quadratic_form_lipschitz (A : E →L[ℝ] E) (M : ℝ)
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |inner (𝕜 := ℝ) u (A u) - inner (𝕜 := ℝ) v (A v)| ≤ 2 * M * ‖u - v‖ := by
  have hid : inner (𝕜 := ℝ) u (A u) - inner (𝕜 := ℝ) v (A v) =
      inner (𝕜 := ℝ) (u - v) (A u) + inner (𝕜 := ℝ) v (A (u - v)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  rw [hid]
  calc
    |inner (𝕜 := ℝ) (u - v) (A u) + inner (𝕜 := ℝ) v (A (u - v))|
        ≤ |inner (𝕜 := ℝ) (u - v) (A u)| + |inner (𝕜 := ℝ) v (A (u - v))| := abs_add _ _
    _ ≤ ‖u - v‖ * ‖A u‖ + ‖v‖ * ‖A (u - v)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖u - v‖ * (M * ‖u‖) + ‖v‖ * (M * ‖u - v‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (hA u) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hA (u - v)) (norm_nonneg _))
    _ = 2 * M * ‖u - v‖ := by rw [hu, hv]; ring

/-- The squared model norm has Lipschitz constant 2M² on the unit sphere. -/
theorem unit_squared_model_norm_lipschitz (A : E →L[ℝ] E) (M : ℝ)
    (hM : 0 ≤ M) (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖) (u v : E)
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |‖A u‖ ^ 2 - ‖A v‖ ^ 2| ≤ 2 * M ^ 2 * ‖u - v‖ := by
  have hd : |‖A u‖ - ‖A v‖| ≤ M * ‖u - v‖ := by
    calc
      |‖A u‖ - ‖A v‖| ≤ ‖A u - A v‖ := abs_norm_sub_norm_le _ _
      _ = ‖A (u - v)‖ := by rw [map_sub]
      _ ≤ M * ‖u - v‖ := hA _
  have hs : ‖A u‖ + ‖A v‖ ≤ 2 * M := by
    have h1 := hA u
    have h2 := hA v
    rw [hu, mul_one] at h1
    rw [hv, mul_one] at h2
    linarith
  calc
    |‖A u‖ ^ 2 - ‖A v‖ ^ 2| = |‖A u‖ - ‖A v‖| * (‖A u‖ + ‖A v‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      ring
    _ ≤ (M * ‖u - v‖) * (2 * M) :=
      mul_le_mul hd hs (add_nonneg (norm_nonneg _) (norm_nonneg _))
        (mul_nonneg hM (norm_nonneg _))
    _ = 2 * M ^ 2 * ‖u - v‖ := by ring

/-- Both BB quotients are invariant under a common nonzero scalar multiple. -/
theorem bb_smul (s v : E) (c : ℝ) (hc : c ≠ 0) :
    bb1 (c • s) (c • v) = bb1 s v ∧ bb2 (c • s) (c • v) = bb2 s v := by
  have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 hc
  constructor
  · simp only [bb1, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    have hid : c * (c * inner (𝕜 := ℝ) s v) = c ^ 2 * inner (𝕜 := ℝ) s v := by ring
    rw [hid, mul_div_mul_left _ _ hc2]
  · simp only [bb2, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_smul_right]
    have hid : c * (c * inner (𝕜 := ℝ) s v) = c ^ 2 * inner (𝕜 := ℝ) s v := by ring
    rw [hid, mul_div_mul_left _ _ hc2]

/-- The normalization map's estimate with the first vector's norm. -/
theorem normalized_difference_le (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ≤ 2 * ‖u - v‖ / ‖u‖ := by
  have hu0 : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hv0 : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hid : (‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v =
      (‖u‖⁻¹ : ℝ) • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹ : ℝ) • v := by
    rw [smul_sub, sub_smul]
    abel
  have hi : |‖u‖⁻¹ - ‖v‖⁻¹| * ‖v‖ = |‖v‖ - ‖u‖| / ‖u‖ := by
    have heq : ‖u‖⁻¹ - ‖v‖⁻¹ = (‖v‖ - ‖u‖) / (‖u‖ * ‖v‖) := by
      field_simp [hu0.ne', hv0.ne']
    rw [heq, abs_div, abs_of_pos (mul_pos hu0 hv0)]
    field_simp [hu0.ne', hv0.ne']
    ring
  rw [hid]
  calc
    ‖(‖u‖⁻¹ : ℝ) • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹ : ℝ) • v‖
        ≤ ‖(‖u‖⁻¹ : ℝ) • (u - v)‖ + ‖(‖u‖⁻¹ - ‖v‖⁻¹ : ℝ) • v‖ := norm_add_le _ _
    _ = ‖u - v‖ / ‖u‖ + |‖v‖ - ‖u‖| / ‖u‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hu0), hi]
      ring
    _ ≤ ‖u - v‖ / ‖u‖ + ‖u - v‖ / ‖u‖ := by
      apply add_le_add_left
      apply div_le_div_of_nonneg_right _ hu0.le
      simpa [abs_sub_comm] using abs_norm_sub_norm_le u v
    _ = 2 * ‖u - v‖ / ‖u‖ := by ring

/-- The normalization estimate stated in the manuscript. -/
theorem normalized_difference_le_min (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ≤
      2 * ‖u - v‖ / min ‖u‖ ‖v‖ := by
  calc
    _ ≤ 2 * ‖u - v‖ / ‖u‖ := normalized_difference_le u v hu hv
    _ ≤ 2 * ‖u - v‖ / min ‖u‖ ‖v‖ :=
      div_le_div_of_nonneg_left (by positivity)
        (lt_min (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv)) (min_le_left _ _)

/-- Frozen BB1 has the stated Lipschitz constant on the unit sphere. -/
theorem frozen_bb1_unit_lipschitz (A : E →L[ℝ] E) (m M : ℝ) (hm : 0 < m)
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖)
    (hco : ∀ z, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z))
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |bb1 u (A u) - bb1 v (A v)| ≤ (2 * M / m ^ 2) * ‖u - v‖ := by
  have ha : m ≤ inner (𝕜 := ℝ) u (A u) := by simpa [hu] using hco u
  have hb : m ≤ inner (𝕜 := ℝ) v (A v) := by simpa [hv] using hco v
  have h := inverse_lipschitz (inner (𝕜 := ℝ) u (A u)) (inner (𝕜 := ℝ) v (A v)) m
    (2 * M * ‖u - v‖) hm ha hb (unit_quadratic_form_lipschitz A M hA u v hu hv)
  calc
    |bb1 u (A u) - bb1 v (A v)| =
        |1 / inner (𝕜 := ℝ) u (A u) - 1 / inner (𝕜 := ℝ) v (A v)| := by simp [bb1, hu, hv]
    _ ≤ (2 * M * ‖u - v‖) / m ^ 2 := h
    _ = (2 * M / m ^ 2) * ‖u - v‖ := by ring

/-- Quotient Lipschitz estimate with the two denominator lower bounds exposed. -/
theorem ratio_lipschitz (a b q r m M δ : ℝ) (hm : 0 < m)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hq : m ^ 2 ≤ q) (hr : m ^ 2 ≤ r)
    (hb : |b| ≤ M) (hd : |a - b| ≤ 2 * M * δ)
    (he : |r - q| ≤ 2 * M ^ 2 * δ) :
    |a / q - b / r| ≤ (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) * δ := by
  have hq0 : 0 < q := (sq_pos_of_pos hm).trans_le hq
  have hr0 : 0 < r := (sq_pos_of_pos hm).trans_le hr
  have hp : m ^ 4 ≤ q * r := by
    have h := mul_le_mul hq hr (sq_nonneg m) hq0.le
    nlinarith only [h]
  have hid : a / q - b / r = (a - b) / q + b * (r - q) / (q * r) := by
    field_simp [hq0.ne', hr0.ne']
    ring_nf
  rw [hid]
  calc
    |(a - b) / q + b * (r - q) / (q * r)|
        ≤ |(a - b) / q| + |b * (r - q) / (q * r)| := abs_add _ _
    _ = |a - b| / q + |b| * |r - q| / (q * r) := by
      rw [abs_div, abs_div, abs_mul, abs_of_pos hq0, abs_of_pos (mul_pos hq0 hr0)]
    _ ≤ (2 * M * δ) / m ^ 2 + (M * (2 * M ^ 2 * δ)) / m ^ 4 := by
      apply add_le_add
      · exact div_le_div (by positivity) hd (sq_pos_of_pos hm) hq
      · exact div_le_div (by positivity)
          (mul_le_mul hb he (abs_nonneg _) hM) (by positivity) hp
    _ = (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) * δ := by ring

/-- Frozen BB2 has the stated Lipschitz constant on the unit sphere. -/
theorem frozen_bb2_unit_lipschitz (A : E →L[ℝ] E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖)
    (hco : ∀ z, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z))
    (u v : E) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    |bb2 u (A u) - bb2 v (A v)| ≤
      (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) * ‖u - v‖ := by
  have hu0 : u ≠ 0 := by intro h; simp [h] at hu
  have hv0 : v ≠ 0 := by intro h; simp [h] at hv
  have hAu : m ≤ ‖A u‖ := by
    simpa [hu] using norm_lower_of_inner_lower u (A u) m hu0 (hco u)
  have hAv : m ≤ ‖A v‖ := by
    simpa [hv] using norm_lower_of_inner_lower v (A v) m hv0 (hco v)
  have hq : m ^ 2 ≤ ‖A u‖ ^ 2 := by
    nlinarith only [mul_self_le_mul_self hm.le hAu]
  have hr : m ^ 2 ≤ ‖A v‖ ^ 2 := by
    nlinarith only [mul_self_le_mul_self hm.le hAv]
  have hb : |inner (𝕜 := ℝ) v (A v)| ≤ M := by
    calc
      |inner (𝕜 := ℝ) v (A v)| ≤ ‖v‖ * ‖A v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (M * ‖v‖) := mul_le_mul_of_nonneg_left (hA v) (norm_nonneg _)
      _ = M := by rw [hv]; ring
  have h := ratio_lipschitz (inner (𝕜 := ℝ) u (A u)) (inner (𝕜 := ℝ) v (A v))
    (‖A u‖ ^ 2) (‖A v‖ ^ 2) m M ‖u - v‖ hm hM (norm_nonneg _)
    hq hr hb (unit_quadratic_form_lipschitz A M hA u v hu hv)
    (by simpa [abs_sub_comm] using unit_squared_model_norm_lipschitz A M hM hA u v hu hv)
  exact h

/-- Both normalized-direction Lipschitz estimates in the manuscript. -/
theorem frozen_steps_directional_lipschitz (A : E →L[ℝ] E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖)
    (hco : ∀ z, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z))
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    |bb1 u (A u) - bb1 v (A v)| ≤
      (2 * M / m ^ 2) * ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ ∧
    |bb2 u (A u) - bb2 v (A v)| ≤
      (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) *
        ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ := by
  have hnu : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u)]
    exact inv_mul_cancel (norm_ne_zero_iff.mpr hu)
  have hnv : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v)]
    exact inv_mul_cancel (norm_ne_zero_iff.mpr hv)
  have huBB := bb_smul u (A u) ‖u‖⁻¹ (inv_ne_zero (norm_ne_zero_iff.mpr hu))
  have hvBB := bb_smul v (A v) ‖v‖⁻¹ (inv_ne_zero (norm_ne_zero_iff.mpr hv))
  constructor
  · have h := frozen_bb1_unit_lipschitz A m M hm hA hco _ _ hnu hnv
    simpa only [map_smul, huBB.1, hvBB.1] using h
  · have h := frozen_bb2_unit_lipschitz A m M hm hM hA hco _ _ hnu hnv
    simpa only [map_smul, huBB.2, hvBB.2] using h

/-- The corresponding estimates with the minimum secant norm in the denominator. -/
theorem frozen_steps_lipschitz_min (A : E →L[ℝ] E) (m M : ℝ)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖)
    (hco : ∀ z, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z))
    (u v : E) (hu : u ≠ 0) (hv : v ≠ 0) :
    |bb1 u (A u) - bb1 v (A v)| ≤
      2 * (2 * M / m ^ 2) * ‖u - v‖ / min ‖u‖ ‖v‖ ∧
    |bb2 u (A u) - bb2 v (A v)| ≤
      2 * (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) * ‖u - v‖ / min ‖u‖ ‖v‖ := by
  have h := frozen_steps_directional_lipschitz A m M hm hM hA hco u v hu hv
  have hn := normalized_difference_le_min u v hu hv
  constructor
  · calc
      _ ≤ (2 * M / m ^ 2) * ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ := h.1
      _ ≤ (2 * M / m ^ 2) * (2 * ‖u - v‖ / min ‖u‖ ‖v‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  · calc
      _ ≤ (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) *
          ‖(‖u‖⁻¹ : ℝ) • u - (‖v‖⁻¹ : ℝ) • v‖ := h.2
      _ ≤ (2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4) *
          (2 * ‖u - v‖ / min ‖u‖ ‖v‖) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring

/-- Exact frozen BB intervals from the two spectral quadratic-form sandwiches. -/
theorem frozen_steps_interval (s w : E) (m M : ℝ) (hs : s ≠ 0)
    (hm : 0 < m) (hmM : m ≤ M)
    (hlo : m * ‖s‖ ^ 2 ≤ inner (𝕜 := ℝ) s w)
    (hhi : inner (𝕜 := ℝ) s w ≤ M * ‖s‖ ^ 2)
    (hlo2 : m * inner (𝕜 := ℝ) s w ≤ ‖w‖ ^ 2)
    (hhi2 : ‖w‖ ^ 2 ≤ M * inner (𝕜 := ℝ) s w) :
    1 / M ≤ bb1 s w ∧ bb1 s w ≤ 1 / m ∧
      1 / M ≤ bb2 s w ∧ bb2 s w ≤ 1 / m := by
  have hM : 0 < M := hm.trans_le hmM
  have hS : 0 < ‖s‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hs)
  have hp : 0 < inner (𝕜 := ℝ) s w := (mul_pos hm hS).trans_le hlo
  have hw : 0 < ‖w‖ ^ 2 := (mul_pos hm hp).trans_le hlo2
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (div_le_div_iff hM hp).mpr (by nlinarith only [hhi])
  · exact (div_le_div_iff hp hm).mpr (by nlinarith only [hlo])
  · exact (div_le_div_iff hM hw).mpr (by nlinarith only [hhi2])
  · exact (div_le_div_iff hw hm).mpr (by nlinarith only [hlo2])

/-- Lower bound for generated frozen secants before the threshold is hit. -/
theorem generated_secant_lower (e w : E) (α m M τ R : ℝ)
    (hm : 0 < m) (hM : 0 < M) (hα : 1 / M ≤ α)
    (hw : m * ‖e‖ ≤ ‖w‖) (hthreshold : τ * R ≤ ‖e‖) :
    (m * τ / M) * R ≤ ‖-α • w‖ := by
  have hα0 : 0 < α := (one_div_pos.mpr hM).trans_le hα
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hα0]
  calc
    (m * τ / M) * R = (1 / M) * (m * (τ * R)) := by ring
    _ ≤ (1 / M) * (m * ‖e‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hthreshold hm.le) (by positivity)
    _ ≤ (1 / M) * ‖w‖ := mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ α * ‖w‖ := mul_le_mul_of_nonneg_right hα (norm_nonneg w)

/-- Exact update-difference identity used in the finite tracking argument. -/
theorem tracking_update_identity (A : E →L[ℝ] E) (e eHat R : E) (α aHat : ℝ) :
    (e - α • (A e + R)) - (eHat - aHat • A eHat) =
      ((e - eHat) - aHat • A (e - eHat)) - (α - aHat) • A e - α • R := by
  simp only [map_sub, smul_add, smul_sub, sub_smul]
  abel

/-- The scalar geometric-series induction behind the finite tracking estimate. -/
theorem scalar_tracking_induction (δ : ℕ → ℝ) (A B Ω : ℝ)
    (hA : 0 ≤ A) (hzero : δ 0 ≤ 0)
    (hstep : ∀ j, δ (j + 1) ≤ A * δ j + B * Ω) :
    ∀ n, δ n ≤ B * Ω * ∑ i ∈ Finset.range n, A ^ i := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    calc
      δ (n + 1) ≤ A * δ n + B * Ω := hstep n
      _ ≤ A * (B * Ω * ∑ i ∈ Finset.range n, A ^ i) + B * Ω :=
        add_le_add_right (mul_le_mul_of_nonneg_left ih hA) _
      _ = B * Ω * ∑ i ∈ Finset.range (n + 1), A ^ i := by
        rw [geom_sum_succ]
        ring

/-- Strictly increasing block endpoints starting at zero cover every index. -/
theorem block_endpoints_cover (t : ℕ → ℕ) (hzero : t 0 = 0)
    (hstep : ∀ i, t i < t (i + 1)) (k : ℕ) :
    ∃ i, t i ≤ k ∧ k < t (i + 1) := by
  have hge : ∀ i, i ≤ t i := by
    intro i
    induction i with
    | zero => omega
    | succ i ih => have h := hstep i; omega
  have hex : ∃ n, k < t n := ⟨k + 1, by have h := hge (k + 1); omega⟩
  let n := Nat.find hex
  have hn : k < t n := Nat.find_spec hex
  have hnpos : 0 < n := by
    by_contra h
    have hz : n = 0 := by omega
    rw [hz, hzero] at hn
    omega
  refine ⟨n - 1, ?_, ?_⟩
  · exact le_of_not_gt (Nat.find_min hex (by change n - 1 < n; omega))
  · simpa only [Nat.sub_add_cancel (show 1 ≤ n by omega)] using hn

/-- An abstract restart bound, conditional on already constructed blocks.

This does not assert that nonlinear BB supplies the blocks: that construction
is a separate remaining obligation of the full localization theorem.
-/
theorem block_restart_envelope (a : ℕ → ℝ) (t : ℕ → ℕ)
    (D γ R : ℝ) (N : ℕ) (hD : 0 ≤ D) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hR : 0 ≤ R)
    (hzero : t 0 = 0) (hstep : ∀ i, t i < t (i + 1))
    (hgap : ∀ i, t (i + 1) ≤ t i + N)
    (hend : ∀ i, a (t i) ≤ γ ^ (t i) * R)
    (hgrowth : ∀ i k, t i ≤ k → k < t (i + 1) → a k ≤ D * a (t i)) :
    ∀ k, a k ≤ (D / γ ^ N) * γ ^ k * R := by
  intro k
  obtain ⟨i, hik, hki⟩ := block_endpoints_cover t hzero hstep k
  have hkN : k ≤ t i + N := by have h := hgap i; omega
  have hp : γ ^ (t i) * γ ^ N ≤ γ ^ k := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hγ.le hγ1 hkN
  have hp' : γ ^ (t i) ≤ γ ^ k / γ ^ N := (le_div_iff (pow_pos hγ N)).mpr hp
  calc
    a k ≤ D * a (t i) := hgrowth i k hik hki
    _ ≤ D * (γ ^ (t i) * R) := mul_le_mul_of_nonneg_left (hend i) hD
    _ = (D * γ ^ (t i)) * R := by ring
    _ ≤ (D * (γ ^ k / γ ^ N)) * R :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp' hD) hR
    _ = (D / γ ^ N) * γ ^ k * R := by ring

/-- A nonnegative derivative comparison against a quadratic, on the unit interval. -/
theorem quadratic_value_lower (f f' : ℝ → ℝ) (a : ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hl : ∀ t ∈ Set.Icc (0 : ℝ) 1, a * t ≤ f' t) :
    a / 2 ≤ f 1 - f 0 := by
  have hg : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => f z - (a / 2) * z ^ 2) (f' t - a * t) t := by
    intro t ht
    convert (hf t ht).sub (((hasDerivAt_id t).pow 2).const_mul (a / 2)) using 1
    simp
    ring
  have hcont : ContinuousOn (fun z : ℝ => f z - (a / 2) * z ^ 2) (Set.Icc 0 1) := by
    intro t ht
    exact (hg t ht).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun z : ℝ => f z - (a / 2) * z ^ 2)
      (interior (Set.Icc 0 1)) := by
    intro t ht
    exact (hg t (interior_subset ht)).differentiableAt.differentiableWithinAt
  have hnonneg : ∀ t ∈ interior (Set.Icc (0 : ℝ) 1),
      0 ≤ deriv (fun z : ℝ => f z - (a / 2) * z ^ 2) t := by
    intro t ht
    rw [(hg t (interior_subset ht)).deriv]
    exact sub_nonneg.mpr (hl t (interior_subset ht))
  have hmon := monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1) hcont hdiff hnonneg
  have h01 := hmon (by simp : (0 : ℝ) ∈ Set.Icc 0 1)
    (by simp : (1 : ℝ) ∈ Set.Icc 0 1) zero_le_one
  norm_num at h01
  linarith only [h01]

/-- The sharp factor 1/2 in the objective comparison, from path derivatives. -/
theorem quadratic_value_bounds (f f' : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t)
    (hl : ∀ t ∈ Set.Icc (0 : ℝ) 1, a * t ≤ f' t)
    (hh : ∀ t ∈ Set.Icc (0 : ℝ) 1, f' t ≤ b * t) :
    a / 2 ≤ f 1 - f 0 ∧ f 1 - f 0 ≤ b / 2 := by
  refine ⟨quadratic_value_lower f f' a hf hl, ?_⟩
  have h := quadratic_value_lower (fun t => -f t) (fun t => -f' t) (-b)
    (fun t ht => (hf t ht).neg) (by intro t ht; change -b * t ≤ -f' t; have hb := hh t ht; linarith only [hb])
  linarith only [h]

/-- The linear-model upper Rayleigh bound follows from the norm bound. -/
theorem inner_model_upper (A : E →L[ℝ] E) (M : ℝ)
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖) (z : E) :
    inner (𝕜 := ℝ) z (A z) ≤ M * ‖z‖ ^ 2 := by
  calc
    inner (𝕜 := ℝ) z (A z) ≤ ‖z‖ * ‖A z‖ := real_inner_le_norm _ _
    _ ≤ ‖z‖ * (M * ‖z‖) := mul_le_mul_of_nonneg_left (hA z) (norm_nonneg z)
    _ = M * ‖z‖ ^ 2 := by ring

/-- The objective comparison from the actual gradient and two-point remainder.

The set S need only contain the segment in question. For the manuscript take
S to be its closed ball, which is convex. Completeness is the Hilbert-space
hypothesis needed by the gradient's Riesz representation.
-/
theorem local_objective_bounds [CompleteSpace E]
    (F : E → ℝ) (G : E → E) (A : E →L[ℝ] E) (S : Set E)
    (xstar e : E) (m M ε : ℝ)
    (hstar : xstar ∈ S) (hGstar : G xstar = 0)
    (hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, xstar + t • e ∈ S)
    (hgrad : ∀ x ∈ S, HasGradientAt F (G x) x)
    (hco : ∀ z, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z))
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖)
    (hrem : ∀ x ∈ S, ∀ y ∈ S, ‖G x - G y - A (x - y)‖ ≤ ε * ‖x - y‖) :
    (m - ε) / 2 * ‖e‖ ^ 2 ≤ F (xstar + e) - F xstar ∧
      F (xstar + e) - F xstar ≤ (M + ε) / 2 * ‖e‖ ^ 2 := by
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun z : ℝ => F (xstar + z • e))
        (inner (𝕜 := ℝ) e (G (xstar + t • e))) t := by
    intro t ht
    have hline : HasDerivAt (fun z : ℝ => xstar + z • e) e t := by
      simpa using (hasDerivAt_const t xstar).add ((hasDerivAt_id t).smul_const e)
    have h := (hgrad _ (hsegment t ht)).hasFDerivAt.comp_hasDerivAt t hline
    simpa only [InnerProductSpace.toDual_apply, real_inner_comm] using h
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (m - ε) * ‖e‖ ^ 2 * t ≤ inner (𝕜 := ℝ) e (G (xstar + t • e)) ∧
      inner (𝕜 := ℝ) e (G (xstar + t • e)) ≤ (M + ε) * ‖e‖ ^ 2 * t := by
    intro t ht
    have hr := hrem (xstar + t • e) (hsegment t ht) xstar hstar
    simp only [hGstar, sub_zero, add_sub_cancel_left, map_smul] at hr
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1] at hr
    have hr' : ‖G (xstar + t • e) - t • A e‖ ≤ (ε * t) * ‖e‖ := by
      nlinarith only [hr]
    have hi := abs_le.mp (inner_remainder_bound e (G (xstar + t • e)) (t • A e) (ε * t) hr')
    rw [real_inner_smul_right] at hi
    have hlo := mul_le_mul_of_nonneg_left (hco e) ht.1
    have hhi := mul_le_mul_of_nonneg_left (inner_model_upper A M hA e) ht.1
    constructor <;> nlinarith only [hi.1, hi.2, hlo, hhi]
  have h := quadratic_value_bounds (fun z : ℝ => F (xstar + z • e))
    (fun t => inner (𝕜 := ℝ) e (G (xstar + t • e)))
    ((m - ε) * ‖e‖ ^ 2) ((M + ε) * ‖e‖ ^ 2) hf
    (fun t ht => (hb t ht).1) (fun t ht => (hb t ht).2)
  simpa only [one_smul, zero_smul, add_zero, mul_div_assoc, div_mul_eq_mul_div] using h

/-- Gradient and error norms are locally equivalent under the two-point estimate. -/
theorem local_gradient_bounds
    (G : E → E) (A : E →L[ℝ] E) (S : Set E) (xstar x : E) (m M ε : ℝ)
    (hstar : xstar ∈ S) (hx : x ∈ S) (hGstar : G xstar = 0)
    (hco : ∀ z, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z))
    (hA : ∀ z, ‖A z‖ ≤ M * ‖z‖)
    (hrem : ∀ z ∈ S, ∀ y ∈ S, ‖G z - G y - A (z - y)‖ ≤ ε * ‖z - y‖) :
    (m - ε) * ‖x - xstar‖ ≤ ‖G x‖ ∧ ‖G x‖ ≤ (M + ε) * ‖x - xstar‖ := by
  by_cases heq : x = xstar
  · simp [heq, hGstar]
  · have hr := hrem x hx xstar hstar
    simp only [hGstar, sub_zero] at hr
    exact secant_norm_bounds (x - xstar) (G x) (A (x - xstar)) m M ε
      (sub_ne_zero.mpr heq) (hco _) (inner_model_upper A M hA _) (hA _) hr

/-- The set whose supremum is the strict-linearization modulus. -/
def remainderRatios (G : E → E) (A : E →L[ℝ] E) (S : Set E) : Set ℝ :=
  {q | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ q = ‖G x - G y - A (x - y)‖ / ‖x - y‖}

/-- Real-valued modulus; use only after proving boundedness of `remainderRatios`. -/
def remainderModulus (G : E → E) (A : E →L[ℝ] E) (S : Set E) : ℝ :=
  sSup (remainderRatios G A S)

/-- Derivation of the two-point remainder estimate from the paper's supremum. -/
theorem remainder_bound_of_sup (G : E → E) (A : E →L[ℝ] E) (S : Set E)
    (hbdd : BddAbove (remainderRatios G A S)) (x y : E) (hx : x ∈ S) (hy : y ∈ S) :
    ‖G x - G y - A (x - y)‖ ≤ remainderModulus G A S * ‖x - y‖ := by
  by_cases heq : x = y
  · subst y
    simp
  · have hmem : ‖G x - G y - A (x - y)‖ / ‖x - y‖ ∈ remainderRatios G A S :=
      ⟨x, hx, y, hy, heq, rfl⟩
    have hsup := le_csSup hbdd hmem
    exact (div_le_iff (norm_pos_iff.mpr (sub_ne_zero.mpr heq))).mp hsup

/-- Monotonicity of the finite supremum modulus under enlargement of the set. -/
theorem remainder_modulus_mono (G : E → E) (A : E →L[ℝ] E) (S T : Set E)
    (hst : S ⊆ T) (hne : (remainderRatios G A S).Nonempty)
    (hbdd : BddAbove (remainderRatios G A T)) :
    remainderModulus G A S ≤ remainderModulus G A T := by
  apply csSup_le hne
  intro q hq
  obtain ⟨x, hx, y, hy, hxy, hq⟩ := hq
  exact le_csSup hbdd ⟨x, hst hx, y, hst hy, hxy, hq⟩

/-- Nonnegativity of the finite supremum modulus, with nonemptiness explicit. -/
theorem remainder_modulus_nonneg (G : E → E) (A : E →L[ℝ] E) (S : Set E)
    (hne : (remainderRatios G A S).Nonempty) (hbdd : BddAbove (remainderRatios G A S)) :
    0 ≤ remainderModulus G A S := by
  obtain ⟨q, hq⟩ := hne
  have hsup := le_csSup hbdd hq
  obtain ⟨x, _hx, y, _hy, _hxy, heq⟩ := hq
  rw [heq] at hsup
  exact (div_nonneg (norm_nonneg _) (norm_nonneg _)).trans hsup

/-- Strict Fréchet differentiability yields a uniform relative remainder on a
small closed ball, including arbitrarily short secants. -/
theorem strict_derivative_closed_ball_estimate (G : E → E) (A : E →L[ℝ] E)
    (xstar : E) (hstrict : HasStrictFDerivAt G A xstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ Metric.closedBall xstar r, ∀ y ∈ Metric.closedBall xstar r,
      ‖G x - G y - A (x - y)‖ ≤ ε * ‖x - y‖ := by
  have hevent : ∀ᶠ p : E × E in 𝓝 (xstar, xstar),
      ‖G p.1 - G p.2 - A (p.1 - p.2)‖ ≤ ε * ‖p.1 - p.2‖ :=
    Asymptotics.isLittleO_iff.mp hstrict hε
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp hevent
  refine ⟨r / 2, by linarith, ?_⟩
  intro x hx y hy
  apply hball (x, y)
  rw [← ball_prod_same, Set.mem_prod]
  exact ⟨(Metric.mem_closedBall.mp hx).trans_lt (half_lt_self hr),
    (Metric.mem_closedBall.mp hy).trans_lt (half_lt_self hr)⟩

/-- A continuously varying derivative supplies the strict two-point estimate. -/
theorem continuous_derivative_closed_ball_estimate (G : E → E)
    (G' : E → E →L[ℝ] E) (xstar : E)
    (hder : ∀ᶠ x in 𝓝 xstar, HasFDerivAt G (G' x) x)
    (hcont : ContinuousAt G' xstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, ∀ x ∈ Metric.closedBall xstar r, ∀ y ∈ Metric.closedBall xstar r,
      ‖G x - G y - G' xstar (x - y)‖ ≤ ε * ‖x - y‖ := by
  exact strict_derivative_closed_ball_estimate G (G' xstar) xstar
    (hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt hder hcont) ε hε

/-- The analytic implication behind the C² corollary: the gradient is strictly
Fréchet differentiable at the point, with its actual Fréchet derivative. -/
theorem c2_gradient_strict [CompleteSpace E] (F : E → ℝ) (xstar : E)
    (hF : ContDiffAt ℝ 2 F xstar) :
    HasStrictFDerivAt (gradient F) (fderiv ℝ (gradient F) xstar) xstar := by
  have hfd : ContDiffAt ℝ 1 (fderiv ℝ F) xstar := hF.fderiv_right (by norm_num)
  have hg : ContDiffAt ℝ 1 (gradient F) xstar := by
    simpa only [gradient] using hfd.continuousLinearMap_comp
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact hg.hasStrictFDerivAt (by norm_num)

end BB.Nonlinear
