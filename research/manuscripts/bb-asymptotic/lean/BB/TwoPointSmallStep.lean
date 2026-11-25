import BB.TwoPointRates

/-!
# Small actual BB1 steps in same-sign projective logarithmic cones

This module proves the quantitative analytic step estimate used to pass from
the exact projective log recurrence to a small norm ratio in every three-step
window. Both the rational square ratio and the actual BB1 update are verified.
-/

noncomputable section
namespace BB

/-- Exact squared norm ratio in terms of previous/current positive projective ratios. -/
def twoPointStepSquare (a b r s : ℝ) : ℝ :=
  (b-a)^2*(s+r^2)/((a*r+b)^2*(s+1))

lemma twoPointStepSquare_small (a b r s ε : ℝ) (ha : 0<a) (hab : a≤b)
    (hr : 0<r) (hs : 0<s) (hrε : r≤ε) (hsε : s≤ε) :
    twoPointStepSquare a b r s ≤ ((b-a)/a)^2*(ε+ε^2) := by
  have hd : a≤a*r+b := by nlinarith only [hab,mul_pos ha hr]
  have hd2 : a^2≤(a*r+b)^2 := pow_le_pow_left ha.le hd 2
  have hden : a^2≤(a*r+b)^2*(s+1) := by
    calc
      a^2 ≤ (a*r+b)^2 := hd2
      _ ≤ (a*r+b)^2*(s+1) := by nlinarith only [mul_nonneg (sq_nonneg (a*r+b)) hs.le]
  have hnum : 0≤(b-a)^2*(s+r^2) := mul_nonneg (sq_nonneg _) (add_nonneg hs.le (sq_nonneg _))
  calc
    twoPointStepSquare a b r s ≤ ((b-a)^2*(s+r^2))/(a^2) :=
      div_le_div_of_nonneg_left hnum (sq_pos_of_pos ha) hden
    _ = ((b-a)/a)^2*(s+r^2) := by field_simp
    _ ≤ ((b-a)/a)^2*(ε+ε^2) := mul_le_mul_of_nonneg_left
      (add_le_add hsε (pow_le_pow_left hr.le hrε 2)) (sq_nonneg _)

lemma twoPointStepSquare_large (a b r s : ℝ) (ha : 0<a) (hab : a≤b)
    (hr : 0<r) (hs : 0<s) :
    twoPointStepSquare a b r s ≤ ((b-a)/a)^2*((1/r)^2+1/s) := by
  have hb : 0<b := ha.trans_le hab
  have har : 0<a*r := mul_pos ha hr
  have hd2 : (a*r)^2≤(a*r+b)^2 := pow_le_pow_left har.le (le_add_of_nonneg_right hb.le) 2
  have hden : a^2*r^2*s≤(a*r+b)^2*(s+1) := by
    calc
      a^2*r^2*s = (a*r)^2*s := by ring
      _ ≤ (a*r+b)^2*s := mul_le_mul_of_nonneg_right hd2 hs.le
      _ ≤ (a*r+b)^2*(s+1) := by nlinarith only [sq_nonneg (a*r+b)]
  have hdenpos : 0<a^2*r^2*s := mul_pos (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hr)) hs
  have hnum : 0≤(b-a)^2*(s+r^2) := mul_nonneg (sq_nonneg _) (add_nonneg hs.le (sq_nonneg _))
  calc
    twoPointStepSquare a b r s ≤ ((b-a)^2*(s+r^2))/(a^2*r^2*s) :=
      div_le_div_of_nonneg_left hnum hdenpos hden
    _ = ((b-a)/a)^2*((1/r)^2+1/s) := by
      field_simp [ha.ne',hr.ne',hs.ne']
      left
      ring

/-- Same-sign logarithmic cones force an exponentially small squared step ratio. -/
theorem twoPointStepSquare_le_of_log_cone (a b r s L : ℝ) (ha : 0<a) (hab : a≤b)
    (hr : 0<r) (hs : 0<s)
    (hcone : (L≤Real.log r ∧ L≤Real.log s) ∨ (Real.log r≤-L ∧ Real.log s≤-L)) :
    twoPointStepSquare a b r s ≤ ((b-a)/a)^2*(Real.exp (-L)+Real.exp (-2*L)) := by
  have hexp : (Real.exp (-L))^2=Real.exp (-2*L) := by
    rw [pow_two,←Real.exp_add]
    congr 1
    ring
  rcases hcone with hlarge | hsmall
  · have hrL : Real.exp L≤r := by simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hlarge.1
    have hsL : Real.exp L≤s := by simpa only [Real.exp_log hs] using Real.exp_le_exp.mpr hlarge.2
    have hir : 1/r≤Real.exp (-L) := by
      calc
        1/r ≤ 1/Real.exp L := one_div_le_one_div_of_le (Real.exp_pos L) hrL
        _ = _ := by rw [one_div,Real.exp_neg]
    have his : 1/s≤Real.exp (-L) := by
      calc
        1/s ≤ 1/Real.exp L := one_div_le_one_div_of_le (Real.exp_pos L) hsL
        _ = _ := by rw [one_div,Real.exp_neg]
    have hir2 : (1/r)^2≤Real.exp (-2*L) := by
      rw [←hexp]
      exact pow_le_pow_left (div_nonneg zero_le_one hr.le) hir 2
    exact (twoPointStepSquare_large a b r s ha hab hr hs).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hir2,his]) (sq_nonneg _))
  · have hrL : r≤Real.exp (-L) := by simpa only [Real.exp_log hr] using Real.exp_le_exp.mpr hsmall.1
    have hsL : s≤Real.exp (-L) := by simpa only [Real.exp_log hs] using Real.exp_le_exp.mpr hsmall.2
    simpa only [hexp] using twoPointStepSquare_small a b r s (Real.exp (-L)) ha hab hr hs hrL hsL

/-- A uniform squared step-ratio bound valid for all positive projective states. -/
theorem twoPointStepSquare_uniform_bound (a b r s : ℝ) (ha : 0<a) (hab : a≤b)
    (hr : 0<r) (hs : 0<s) :
    twoPointStepSquare a b r s≤((b-a)/a)^2 := by
  have haux : s+r^2≤(r+1)^2*(s+1) := by
    nlinarith only [hr.le,hs.le,mul_nonneg hr.le hs.le,mul_nonneg (sq_nonneg r) hs.le]
  have hbase : a*(r+1)≤a*r+b := by nlinarith only [hab]
  have hbase0 : 0≤a*(r+1) := mul_nonneg ha.le (by linarith only [hr.le])
  have hden : a^2*(s+r^2)≤(a*r+b)^2*(s+1) := by
    calc
      a^2*(s+r^2) ≤ a^2*((r+1)^2*(s+1)) := mul_le_mul_of_nonneg_left haux (sq_nonneg a)
      _ = (a*(r+1))^2*(s+1) := by ring
      _ ≤ (a*r+b)^2*(s+1) := mul_le_mul_of_nonneg_right
        (pow_le_pow_left hbase0 hbase 2) (by linarith only [hs.le])
  have hsum : 0<s+r^2 := add_pos_of_pos_of_nonneg hs (sq_nonneg r)
  have hnum : 0≤(b-a)^2*(s+r^2) := mul_nonneg (sq_nonneg _) hsum.le
  calc
    twoPointStepSquare a b r s ≤ ((b-a)^2*(s+r^2))/(a^2*(s+r^2)) :=
      div_le_div_of_nonneg_left hnum (mul_pos (sq_pos_of_pos ha) hsum) hden
    _ = ((b-a)/a)^2 := by field_simp [ha.ne',hsum.ne']; ring

lemma normTwo_sq (x y : ℝ) : (normTwo x y)^2=x^2+y^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- The displayed rational quantity is the actual BB1 squared norm ratio. -/
theorem two_point_step_norm_square (a b xp yp x y : ℝ) (ha : 0<a) (hab : a<b)
    (hxp : xp≠0) (hyp : yp≠0) (hy : y≠0) :
    (normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y)^2 =
      twoPointStepSquare a b (ratioTwo xp yp) (ratioTwo x y) := by
  have hden : a*xp^2+b*yp^2≠0 := (add_pos
    (mul_pos ha (sq_pos_of_ne_zero hxp)) (mul_pos (ha.trans hab) (sq_pos_of_ne_zero hyp))).ne'
  rw [div_pow,normTwo_sq,normTwo_sq]
  unfold twoPointStepSquare ratioTwo bb1Two
  field_simp [hden,hyp,hy]
  ring

/-- The actual norm ratio version of the logarithmic cone estimate. -/
theorem two_point_step_norm_le_of_log_cone (a b xp yp x y L : ℝ)
    (ha : 0<a) (hab : a<b) (hxp : xp≠0) (hyp : yp≠0) (hx : x≠0) (hy : y≠0)
    (hcone : (L≤Real.log (ratioTwo xp yp) ∧ L≤Real.log (ratioTwo x y)) ∨
      (Real.log (ratioTwo xp yp)≤-L ∧ Real.log (ratioTwo x y)≤-L)) :
    normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y ≤
      Real.sqrt (((b-a)/a)^2*(Real.exp (-L)+Real.exp (-2*L))) := by
  have hnonneg : 0≤normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = Real.sqrt ((normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y)^2) :=
      (Real.sqrt_sq hnonneg).symm
    _ = Real.sqrt (twoPointStepSquare a b (ratioTwo xp yp) (ratioTwo x y)) := by
      rw [two_point_step_norm_square a b xp yp x y ha hab hxp hyp hy]
    _ ≤ _ := Real.sqrt_le_sqrt (twoPointStepSquare_le_of_log_cone a b (ratioTwo xp yp) (ratioTwo x y) L
      ha hab.le (div_pos (sq_pos_of_ne_zero hxp) (sq_pos_of_ne_zero hyp))
      (div_pos (sq_pos_of_ne_zero hx) (sq_pos_of_ne_zero hy)) hcone)

/-- Direct interface for consecutive indices of a genuine delayed BB1 trajectory. -/
theorem bb1_two_norm_ratio_le_of_log_cone (a b : ℝ) (ha : 0<a) (hab : a<b)
    (x y : ℕ → ℝ) (n : ℕ) (L : ℝ)
    (hxp : x n≠0) (hyp : y n≠0) (hx : x (n+1)≠0) (hy : y (n+1)≠0)
    (hxu : x (n+2)=(1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : y (n+2)=(1-bb1Two a b (x n) (y n)*b)*y (n+1))
    (hcone : (L≤Real.log (ratioTwo (x n) (y n)) ∧ L≤Real.log (ratioTwo (x (n+1)) (y (n+1)))) ∨
      (Real.log (ratioTwo (x n) (y n))≤-L ∧ Real.log (ratioTwo (x (n+1)) (y (n+1)))≤-L)) :
    normTwo (x (n+2)) (y (n+2))/normTwo (x (n+1)) (y (n+1)) ≤
      Real.sqrt (((b-a)/a)^2*(Real.exp (-L)+Real.exp (-2*L))) := by
  rw [hxu,hyu]
  exact two_point_step_norm_le_of_log_cone a b (x n) (y n) (x (n+1)) (y (n+1)) L
    ha hab hxp hyp hx hy hcone


/-- Every actual two-eigenvalue BB1 step has the uniform original norm bound. -/
theorem two_point_step_norm_le (a b xp yp x y : ℝ)
    (ha : 0<a) (hab : a<b) (hxp : xp≠0) (hyp : yp≠0) (hx : x≠0) (hy : y≠0) :
    normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y ≤ (b-a)/a := by
  have hnonneg : 0≤normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  calc
    _ = Real.sqrt ((normTwo ((1-bb1Two a b xp yp*a)*x) ((1-bb1Two a b xp yp*b)*y)/normTwo x y)^2) :=
      (Real.sqrt_sq hnonneg).symm
    _ = Real.sqrt (twoPointStepSquare a b (ratioTwo xp yp) (ratioTwo x y)) := by
      rw [two_point_step_norm_square a b xp yp x y ha hab hxp hyp hy]
    _ ≤ Real.sqrt (((b-a)/a)^2) := Real.sqrt_le_sqrt
      (twoPointStepSquare_uniform_bound a b (ratioTwo xp yp) (ratioTwo x y) ha hab.le
        (div_pos (sq_pos_of_ne_zero hxp) (sq_pos_of_ne_zero hyp))
        (div_pos (sq_pos_of_ne_zero hx) (sq_pos_of_ne_zero hy)))
    _ = (b-a)/a := Real.sqrt_sq (div_nonneg (sub_nonneg.mpr hab.le) ha.le)

/-- Uniform norm-ratio bound at any actual delayed-orbit index. -/
theorem bb1_two_norm_ratio_le (a b : ℝ) (ha : 0<a) (hab : a<b)
    (x y : ℕ → ℝ) (n : ℕ)
    (hxp : x n≠0) (hyp : y n≠0) (hx : x (n+1)≠0) (hy : y (n+1)≠0)
    (hxu : x (n+2)=(1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : y (n+2)=(1-bb1Two a b (x n) (y n)*b)*y (n+1)) :
    normTwo (x (n+2)) (y (n+2))/normTwo (x (n+1)) (y (n+1)) ≤ (b-a)/a := by
  rw [hxu,hyu]
  exact two_point_step_norm_le a b (x n) (y n) (x (n+1)) (y (n+1)) ha hab hxp hyp hx hy

end BB
