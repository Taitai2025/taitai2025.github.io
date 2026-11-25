import BB.Endpoint

/-!
# Exact two-eigenvalue calculations

The quotient below is the actual BB1 quotient of a real gradient pair.
This file proves its endpoint orbit and projective recurrence algebra.
-/

namespace BB
noncomputable section

def bb1Two (a b x y : ℝ) : ℝ := (x^2 + y^2) / (a*x^2 + b*y^2)
def bb2Two (a b x y : ℝ) : ℝ := (a*x^2 + b*y^2) / (a^2*x^2 + b^2*y^2)
def ratioTwo (x y : ℝ) : ℝ := x^2 / y^2
def normTwo (x y : ℝ) : ℝ := Real.sqrt (x^2 + y^2)

theorem bb1_two_pos {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < bb1Two a b x y := by
  have hx : 0 ≤ x^2 := sq_nonneg x
  have hy : 0 ≤ y^2 := sq_nonneg y
  rcases hxy with h | h
  · exact div_pos (by nlinarith [sq_pos_of_ne_zero h])
      (by nlinarith [sq_pos_of_ne_zero h, mul_pos ha (sq_pos_of_ne_zero h),
        mul_nonneg (le_of_lt hb) hy])
  · exact div_pos (by nlinarith [sq_pos_of_ne_zero h])
      (by nlinarith [sq_pos_of_ne_zero h, mul_pos hb (sq_pos_of_ne_zero h),
        mul_nonneg (le_of_lt ha) hx])

theorem balanced_bb1_step {a b x y : ℝ} (hx : x ≠ 0)
    (hbalance : x^2 = y^2) : bb1Two a b x y = 2 / (a + b) := by
  unfold bb1Two
  rw [← hbalance]
  have hxsq : x^2 ≠ 0 := pow_ne_zero 2 hx
  by_cases hs : a + b = 0
  · have hden : a*x^2 + b*x^2 = 0 := by nlinarith [congrArg (fun t : ℝ => t*x^2) hs]
    simp [hs, hden]
  · rw [show a*x^2+b*x^2 = (a+b)*x^2 by ring]
    field_simp [hs, hxsq]
    ring

theorem weighted_balanced_bb2_step {a b x y : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hx : x ≠ 0)
    (hbalance : a*x^2 = b*y^2) : bb2Two a b x y = 2 / (a + b) := by
  have hden : 0 < a^2*x^2 + b^2*y^2 := by
    nlinarith [mul_pos (sq_pos_of_pos ha) (sq_pos_of_ne_zero hx),
      mul_nonneg (sq_nonneg b) (sq_nonneg y)]
  unfold bb2Two
  apply (div_eq_div_iff (ne_of_gt hden) (ne_of_gt (by linarith : 0 < a+b))).mpr
  nlinarith [congrArg (fun t : ℝ => (a-b)*t) hbalance]

theorem endpoint_left_multiplier {a b : ℝ} (hs : a + b ≠ 0) :
    1 - (2 / (a+b))*a = rate a b := by
  unfold rate
  field_simp [hs, show b+a ≠ 0 by simpa only [add_comm] using hs]
  ring

theorem endpoint_right_multiplier {a b : ℝ} (hs : a + b ≠ 0) :
    1 - (2 / (a+b))*b = -(rate a b) := by
  unfold rate
  field_simp [hs, show b+a ≠ 0 by simpa only [add_comm] using hs]
  ring

theorem endpoint_square_orbit (c x y : ℝ) (k : ℕ) :
    (c^k*x)^2 + ((-c)^k*y)^2 = (c^k)^2 * (x^2+y^2) := by
  have hneg : ((-c)^k)^2 = (c^k)^2 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, neg_sq,
      ← pow_mul, Nat.mul_comm 2 k, pow_mul]
  rw [mul_pow, mul_pow, hneg]
  ring

theorem endpoint_norm_orbit {c : ℝ} (hc : 0 ≤ c) (x y : ℝ) (k : ℕ) :
    normTwo (c^k*x) ((-c)^k*y) = c^k * normTwo x y := by
  unfold normTwo
  rw [endpoint_square_orbit, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hc k)]

theorem endpoint_balance_orbit (c x y : ℝ) (h : x^2 = y^2) (k : ℕ) :
    (c^k*x)^2 = ((-c)^k*y)^2 := by
  have hneg : ((-c)^k)^2 = (c^k)^2 := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, neg_sq,
      ← pow_mul, Nat.mul_comm 2 k, pow_mul]
  rw [mul_pow, mul_pow, hneg, h]

/-- The displayed endpoint formula is an actual nonterminating matched BB1 orbit. -/
theorem exact_endpoint_orbit {a b x y : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) (hbal : x^2 = y^2) :
    ∀ k : ℕ,
      bb1Two a b ((rate a b)^k*x) ((-(rate a b))^k*y) = 2/(a+b) ∧
      (1 - (2/(a+b))*a) * ((rate a b)^k*x) = (rate a b)^(k+1)*x ∧
      (1 - (2/(a+b))*b) * ((-(rate a b))^k*y) = (-(rate a b))^(k+1)*y ∧
      normTwo ((rate a b)^k*x) ((-(rate a b))^k*y) =
        (rate a b)^k * normTwo x y := by
  intro k
  have hc : 0 < rate a b := rate_pos ha hab
  have hs : a+b ≠ 0 := ne_of_gt (by linarith : 0 < a+b)
  refine ⟨balanced_bb1_step (mul_ne_zero (pow_ne_zero k (ne_of_gt hc)) hx)
      (endpoint_balance_orbit _ _ _ hbal k), ?_, ?_,
      endpoint_norm_orbit (le_of_lt hc) x y k⟩
  · rw [endpoint_left_multiplier hs, pow_succ]
    ring
  · rw [endpoint_right_multiplier hs, pow_succ]
    ring

/-- A reciprocal mean represented by the positive projective ratio. -/
theorem two_point_multiplier_ratio {a b z : ℝ}
    (ha : 0 < a) (hab : a < b) (hz : 0 < z) :
    (1-a/((a*z+b)/(z+1))) / (1-b/((a*z+b)/(z+1))) = -1/z := by
  have hd : a*z+b ≠ 0 := ne_of_gt (by nlinarith [mul_pos ha hz])
  have hz1 : z+1 ≠ 0 := ne_of_gt (by linarith : 0 < z+1)
  have hba : a-b ≠ 0 := ne_of_lt (sub_neg.mpr hab)
  have hleft : 1-a/((a*z+b)/(z+1)) = (b-a)/(a*z+b) := by
    field_simp [hd, hz1]
    ring
  have hright : 1-b/((a*z+b)/(z+1)) = (a-b)*z/(a*z+b) := by
    field_simp [hd, hz1]
    ring
  rw [hleft, hright]
  field_simp [hd, hba, ne_of_gt hz]
  ring

theorem two_point_step_mean {a b x y : ℝ} (hy : y ≠ 0) :
    bb1Two a b x y = (ratioTwo x y + 1) / (a * ratioTwo x y + b) := by
  unfold bb1Two ratioTwo
  have hy2 : y^2 ≠ 0 := pow_ne_zero 2 hy
  field_simp

/-- The exact algebraic projective recurrence in Proposition `prop:2d-instab`. -/
theorem two_point_ratio_recurrence {a b xp yp x y : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hxp : xp ≠ 0) (hyp : yp ≠ 0) (hy : y ≠ 0) :
    ratioTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y) =
      ratioTwo x y / (ratioTwo xp yp)^2 := by
  have hx2 : 0 < xp^2 := sq_pos_of_ne_zero hxp
  have hy2 : 0 < yp^2 := sq_pos_of_ne_zero hyp
  have hden : a*xp^2+b*yp^2 ≠ 0 := ne_of_gt (by
    nlinarith [mul_pos ha hx2, mul_pos (lt_trans ha hab) hy2])
  have hab0 : a-b ≠ 0 := ne_of_lt (sub_neg.mpr hab)
  have hleft : 1-bb1Two a b xp yp*a = (b-a)*yp^2/(a*xp^2+b*yp^2) := by
    unfold bb1Two
    field_simp [hden]
    ring
  have hright : 1-bb1Two a b xp yp*b = (a-b)*xp^2/(a*xp^2+b*yp^2) := by
    unfold bb1Two
    field_simp [hden]
    ring
  rw [hleft, hright]
  unfold ratioTwo
  field_simp [hden, hab0, hxp, hyp, hy]
  ring

theorem matched_ratio_recurrence {a b x y : ℝ}
    (ha : 0 < a) (hab : a < b) (hx : x ≠ 0) (hy : y ≠ 0) :
    ratioTwo ((1-bb1Two a b x y*a)*x) ((1-bb1Two a b x y*b)*y) =
      (ratioTwo x y)⁻¹ := by
  rw [two_point_ratio_recurrence ha hab hx hy hy]
  unfold ratioTwo
  field_simp
  ring

theorem log_ratio_recurrence {znext zcur zprev : ℝ}
    (hc : 0 < zcur) (hp : 0 < zprev)
    (hrec : znext = zcur / zprev^2) :
    Real.log znext = Real.log zcur - 2 * Real.log zprev := by
  rw [hrec, Real.log_div (ne_of_gt hc) (pow_ne_zero 2 (ne_of_gt hp)), Real.log_pow]
  norm_num

end
end BB
