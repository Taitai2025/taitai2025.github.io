import BB.Endpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Literal scalar reparameterizations used in the source -/

namespace BB

theorem rate_eq_condition_number (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    rate a b = (b/a-1)/(b/a+1) := by
  unfold rate
  have hb : 0 < b := ha.trans_le hab
  have hab0 : b+a ≠ 0 := ne_of_gt (by linarith)
  have hκ0 : b/a+1 ≠ 0 := ne_of_gt (by positivity)
  field_simp [ha.ne',hab0,hκ0]

theorem sharp_line_ratio_bb1 (m M : ℝ) (hm : 0 < m) (hM : 0 < M) :
    Real.sqrt (m^2/M^2) = m/M := by
  rw [← div_pow,Real.sqrt_sq (div_nonneg hm.le hM.le)]

theorem sharp_line_ratio_bb2 (m M : ℝ) (hm : 0 < m) (hM : 0 < M) :
    Real.sqrt (m^3/M^3) = (m/M)^((3:ℝ)/2) := by
  rw [← div_pow,Real.sqrt_eq_rpow,← Real.rpow_natCast (m/M) 3,
    ← Real.rpow_mul (div_nonneg hm.le hM.le)]
  congr 1
  norm_num

end BB
