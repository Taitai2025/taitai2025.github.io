import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# The endpoint certificate

Source: `submission/manuscript/main.tex`, Lemmas `lem:endpoint-ineq`
and `lem:cohomology`. All logarithms in this file have explicitly positive
arguments. In particular `Real.log 0 = 0` is never used to model termination.
-/

namespace BB

noncomputable section

def rate (a b : ℝ) : ℝ := (b - a) / (b + a)
def leftWeight (a b : ℝ) : ℝ := b / (a + b)
def rightWeight (a b : ℝ) : ℝ := a / (a + b)

theorem rate_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < rate a b := by
  unfold rate
  exact div_pos (sub_pos.mpr hab) (by linarith)

theorem rate_lt_one {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    rate a b < 1 := by
  unfold rate
  apply (div_lt_one (by linarith : 0 < b + a)).mpr
  linarith

theorem endpoint_weights_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < leftWeight a b ∧ 0 < rightWeight a b := by
  constructor
  · exact div_pos (by linarith) (by linarith)
  · exact div_pos ha (by linarith)

theorem endpoint_weights_sum {a b : ℝ} (hs : a + b ≠ 0) :
    leftWeight a b + rightWeight a b = 1 := by
  unfold leftWeight rightWeight
  field_simp
  ring

theorem rate_mono_interval {a b A B : ℝ}
    (hA : 0 < A) (hAa : A ≤ a) (hab : a ≤ b) (hbB : b ≤ B) :
    rate a b ≤ rate A B := by
  have ha : 0 < a := lt_of_lt_of_le hA hAa
  have hs : 0 < b + a := by linarith
  have hS : 0 < B + A := by linarith
  unfold rate
  apply (div_le_div_iff hs hS).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hAa) (le_of_lt hS),
    mul_nonneg (sub_nonneg.mpr hbB) (le_of_lt ha)]

/-- The two positive quantities whose weighted arithmetic mean is one. -/
theorem scaled_endpoint_mean {a b u : ℝ}
    (ha : 0 < a) (hab : a < b) (hu : 0 < u) :
    leftWeight a b * (((u - a) / u) / rate a b) +
      rightWeight a b * (((b - u) / u) / rate a b) = 1 := by
  unfold leftWeight rightWeight rate
  have hs : a + b ≠ 0 := ne_of_gt (by linarith : 0 < a + b)
  have hd : b - a ≠ 0 := ne_of_gt (sub_pos.mpr hab)
  field_simp
  ring

def endpointLog (a b u : ℝ) : ℝ :=
  leftWeight a b * Real.log ((u - a) / u) +
    rightWeight a b * Real.log ((b - u) / u)

/-- Interior logarithmic form of the endpoint inequality. -/
theorem endpoint_log_le {a b u : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b) :
    endpointLog a b u ≤ Real.log (rate a b) := by
  have hab : a < b := lt_trans hau hub
  have hu : 0 < u := lt_trans ha hau
  have hc : 0 < rate a b := rate_pos ha hab
  have hx : 0 < (u - a) / u := div_pos (sub_pos.mpr hau) hu
  have hy : 0 < (b - u) / u := div_pos (sub_pos.mpr hub) hu
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  have hs := endpoint_weights_sum (ne_of_gt (by linarith : 0 < a + b))
  have hm := scaled_endpoint_mean ha hab hu
  have hxlog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hx hc)) (le_of_lt hp)
  have hylog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hc)) (le_of_lt hq)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hc)] at hxlog
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hc)] at hylog
  have hslog : leftWeight a b * Real.log (rate a b) +
      rightWeight a b * Real.log (rate a b) = Real.log (rate a b) := by
    rw [← add_mul, hs, one_mul]
  unfold endpointLog
  linarith only [hxlog, hylog, hslog, hm, hs]

/-- Strictness away from the midpoint, proved without assuming an AM--GM equality case. -/
theorem endpoint_log_lt_of_ne_midpoint {a b u : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b)
    (hne : u ≠ (a + b) / 2) :
    endpointLog a b u < Real.log (rate a b) := by
  have hab : a < b := lt_trans hau hub
  have hu : 0 < u := lt_trans ha hau
  have hc : 0 < rate a b := rate_pos ha hab
  have hx : 0 < (u - a) / u := div_pos (sub_pos.mpr hau) hu
  have hy : 0 < (b - u) / u := div_pos (sub_pos.mpr hub) hu
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  have hs := endpoint_weights_sum (ne_of_gt (by linarith : 0 < a + b))
  have hm := scaled_endpoint_mean ha hab hu
  have hxne : ((u - a) / u) / rate a b ≠ 1 := by
    intro he
    have he' : (u - a) / u = rate a b := (div_eq_one_iff_eq (ne_of_gt hc)).mp he
    unfold rate at he'
    have he'' := (div_eq_div_iff (ne_of_gt hu)
      (ne_of_gt (by linarith : 0 < b + a))).mp he'
    have hezero : a * (2*u - (a+b)) = 0 := by nlinarith only [he'']
    have helinear : 2*u - (a+b) = 0 :=
      (mul_eq_zero.mp hezero).resolve_left (ne_of_gt ha)
    have he''' : u = (a + b) / 2 := by linarith only [helinear]
    exact hne he'''
  have hxlog := mul_lt_mul_of_pos_left
    (Real.log_lt_sub_one_of_pos (div_pos hx hc) hxne) hp
  have hylog := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy hc)) (le_of_lt hq)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt hc)] at hxlog
  rw [Real.log_div (ne_of_gt hy) (ne_of_gt hc)] at hylog
  have hslog : leftWeight a b * Real.log (rate a b) +
      rightWeight a b * Real.log (rate a b) = Real.log (rate a b) := by
    rw [← add_mul, hs, one_mul]
  unfold endpointLog
  linarith only [hxlog, hylog, hslog, hm, hs]

theorem endpoint_log_midpoint {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    endpointLog a b ((a + b) / 2) = Real.log (rate a b) := by
  have hs0 : a + b ≠ 0 := ne_of_gt (by linarith : 0 < a + b)
  have hleft : (((a + b) / 2 - a) / ((a + b) / 2)) = rate a b := by
    unfold rate
    field_simp [hs0, show b + a ≠ 0 by linarith]
    ring
  have hright : ((b - (a + b) / 2) / ((a + b) / 2)) = rate a b := by
    unfold rate
    field_simp [hs0, show b + a ≠ 0 by linarith]
    ring
  unfold endpointLog
  rw [hleft, hright, ← add_mul, endpoint_weights_sum hs0, one_mul]

theorem endpoint_log_eq_iff {a b u : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b) :
    endpointLog a b u = Real.log (rate a b) ↔ u = (a + b) / 2 := by
  constructor
  · intro he
    by_contra hne
    exact (ne_of_lt (endpoint_log_lt_of_ne_midpoint ha hau hub hne)) he
  · intro he
    rw [he]
    exact endpoint_log_midpoint ha (lt_trans hau hub)

def endpointProduct (a b u : ℝ) : ℝ :=
  ((u - a) / u) ^ (leftWeight a b) *
    ((b - u) / u) ^ (rightWeight a b)

theorem endpoint_product_eq_exp {a b u : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b) :
    endpointProduct a b u = Real.exp (endpointLog a b u) := by
  have hu : 0 < u := lt_trans ha hau
  rw [endpointProduct, Real.rpow_def_of_pos (div_pos (sub_pos.mpr hau) hu),
    Real.rpow_def_of_pos (div_pos (sub_pos.mpr hub) hu), ← Real.exp_add]
  congr 1
  unfold endpointLog
  ring

/-- Full closed-interval version, including the zero factors at either endpoint. -/
theorem endpoint_product_le {a b u : ℝ}
    (ha : 0 < a) (hab : a < b) (hu : u ∈ Set.Icc a b) :
    endpointProduct a b u ≤ rate a b := by
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  rcases eq_or_lt_of_le hu.1 with h | hau
  · subst u
    simp only [endpointProduct, sub_self, zero_div, Real.zero_rpow (ne_of_gt hp), zero_mul]
    exact le_of_lt (rate_pos ha hab)
  · rcases eq_or_lt_of_le hu.2 with h | hub
    · subst u
      simp only [endpointProduct, sub_self, zero_div, Real.zero_rpow (ne_of_gt hq), mul_zero]
      exact le_of_lt (rate_pos ha hab)
    · rw [endpoint_product_eq_exp ha hau hub]
      exact (Real.exp_le_exp.mpr (endpoint_log_le ha hau hub)).trans_eq
        (Real.exp_log (rate_pos ha hab))

theorem endpoint_product_eq_iff {a b u : ℝ}
    (ha : 0 < a) (hab : a < b) (hu : u ∈ Set.Icc a b) :
    endpointProduct a b u = rate a b ↔ u = (a + b) / 2 := by
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  rcases eq_or_lt_of_le hu.1 with h | hau
  · subst u
    have hn : a ≠ (a + b) / 2 := by linarith
    simp only [endpointProduct, sub_self, zero_div, Real.zero_rpow (ne_of_gt hp), zero_mul]
    exact iff_of_false (ne_of_lt (rate_pos ha hab)) hn
  · rcases eq_or_lt_of_le hu.2 with h | hub
    · subst u
      have hn : b ≠ (a + b) / 2 := by linarith
      simp only [endpointProduct, sub_self, zero_div, Real.zero_rpow (ne_of_gt hq), mul_zero]
      exact iff_of_false (ne_of_lt (rate_pos ha hab)) hn
    · rw [endpoint_product_eq_exp ha hau hub, ← Real.exp_log (rate_pos ha hab),
        Real.exp_injective.eq_iff]
      exact endpoint_log_eq_iff ha hau hub

def endpointPotential (a b wa wb : ℝ) : ℝ :=
  -(leftWeight a b / 2) * Real.log wa -
    (rightWeight a b / 2) * Real.log wb

def endpointDefect (a b u : ℝ) : ℝ := Real.log (rate a b) - endpointLog a b u

theorem endpoint_defect_nonneg {a b u : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b) :
    0 ≤ endpointDefect a b u := sub_nonneg.mpr (endpoint_log_le ha hau hub)

theorem endpoint_defect_eq_zero_iff {a b u : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b) :
    endpointDefect a b u = 0 ↔ u = (a + b) / 2 := by
  unfold endpointDefect
  rw [sub_eq_zero, eq_comm]
  exact endpoint_log_eq_iff ha hau hub

/-- The exact coboundary identity; `R` is the squared norm multiplier.
The positivity assumptions are the original nonterminal endpoint domain. -/
theorem endpoint_cohomology {a b u wa wb R : ℝ}
    (ha : 0 < a) (hau : a < u) (hub : u < b)
    (hwa : 0 < wa) (hwb : 0 < wb) (hR : 0 < R) :
    Real.log R / 2 = Real.log (rate a b) - endpointDefect a b u +
      endpointPotential a b (((u - a) / u)^2 * wa / R)
        (((b - u) / u)^2 * wb / R) - endpointPotential a b wa wb := by
  have hu : 0 < u := lt_trans ha hau
  have hx : 0 < (u - a) / u := div_pos (sub_pos.mpr hau) hu
  have hy : 0 < (b - u) / u := div_pos (sub_pos.mpr hub) hu
  have hs := endpoint_weights_sum (ne_of_gt (by linarith : 0 < a + b))
  have lx : Real.log (((u - a) / u)^2 * wa / R) =
      2 * Real.log ((u - a) / u) + Real.log wa - Real.log R := by
    rw [Real.log_div (ne_of_gt (mul_pos (sq_pos_of_pos hx) hwa)) (ne_of_gt hR),
      Real.log_mul (ne_of_gt (sq_pos_of_pos hx)) (ne_of_gt hwa), Real.log_pow]
    norm_num
  have ly : Real.log (((b - u) / u)^2 * wb / R) =
      2 * Real.log ((b - u) / u) + Real.log wb - Real.log R := by
    rw [Real.log_div (ne_of_gt (mul_pos (sq_pos_of_pos hy) hwb)) (ne_of_gt hR),
      Real.log_mul (ne_of_gt (sq_pos_of_pos hy)) (ne_of_gt hwb), Real.log_pow]
    norm_num
  unfold endpointPotential endpointDefect endpointLog
  rw [lx, ly]
  have hslog : leftWeight a b * Real.log R +
      rightWeight a b * Real.log R = Real.log R := by
    rw [← add_mul, hs, one_mul]
  linarith only [hslog]

end
end BB
