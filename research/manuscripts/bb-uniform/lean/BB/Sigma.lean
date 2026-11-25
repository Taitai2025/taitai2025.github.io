import BB.Endpoint

noncomputable section
namespace BB

/-- The explicit transverse scale chosen in the nonlinear counterexample. -/
def counterexampleSigma (a b : ℝ) : ℝ := (a / b) ^ (5 / 4 : ℝ)

theorem counterexampleSigma_conditions {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < counterexampleSigma a b ∧
      (counterexampleSigma a b * b)^2 < a^2 ∧
      (1-endpointRate a b)*a^2 <
        (1+endpointRate a b)*(counterexampleSigma a b*b)^2 := by
  have hb : 0 < b := ha.trans hab
  have hr : 0 < a/b := div_pos ha hb
  have hr1 : a/b < 1 := (div_lt_one hb).2 hab
  have hsig : 0 < counterexampleSigma a b := Real.rpow_pos_of_pos hr _
  have hsquare : counterexampleSigma a b ^ 2 = (a/b) ^ (5/2:ℝ) := by
    unfold counterexampleSigma
    rw [← Real.rpow_natCast ((a/b)^(5/4:ℝ)) 2, ← Real.rpow_mul hr.le]
    norm_num
  have hlo : (a/b)^3 < counterexampleSigma a b^2 := by
    rw [hsquare, ← Real.rpow_natCast (a/b) 3]
    exact Real.rpow_lt_rpow_of_exponent_gt hr hr1 (by norm_num)
  have hhi : counterexampleSigma a b^2 < (a/b)^2 := by
    rw [hsquare, ← Real.rpow_natCast (a/b) 2]
    exact Real.rpow_lt_rpow_of_exponent_gt hr hr1 (by norm_num)
  have hupper : (counterexampleSigma a b*b)^2 < a^2 := by
    have h := mul_lt_mul_of_pos_right hhi (sq_pos_of_pos hb)
    simpa only [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hb.ne'), ← mul_pow] using h
  have hlower : a^3 < counterexampleSigma a b^2*b^3 := by
    have h := mul_lt_mul_of_pos_right hlo (pow_pos hb 3)
    simpa only [div_pow, div_mul_cancel₀ _ (pow_ne_zero 3 hb.ne')] using h
  refine ⟨hsig, hupper, ?_⟩
  have habp : 0 < b+a := add_pos hb ha
  apply (mul_lt_mul_right habp).mp
  have hid : (1-endpointRate a b)*a^2*(b+a) = 2*a^3 := by
    unfold endpointRate
    field_simp
    <;> ring
  have hid' : (1+endpointRate a b)*(counterexampleSigma a b*b)^2*(b+a) =
      2*counterexampleSigma a b^2*b^3 := by
    unfold endpointRate
    field_simp
    <;> ring
  rw [hid,hid']
  nlinarith only [hlower]

end BB
