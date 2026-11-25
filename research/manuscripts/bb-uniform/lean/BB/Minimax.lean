import BB.Regularization

noncomputable section

namespace BB

open Real

/-- Endpoint monomials with an arbitrary exponent p in (0,1). -/
def monomialMultiplier (a b p τ : ℝ) : ℝ :=
  geometricProduct p ((τ - a) / τ) ((b - τ) / τ)

/-- The reciprocal step at which this endpoint monomial is largest. -/
def monomialMaximizer (a b p : ℝ) : ℝ := a * b / (b * (1 - p) + a * p)

/-- The value of the largest one-step endpoint monomial. -/
def monomialMaximum (a b p : ℝ) : ℝ :=
  geometricProduct p ((b - a) * p / b) ((b - a) * (1 - p) / a)

theorem monomial_denominator_pos {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) : 0 < b * (1 - p) + a * p := by
  have hb := ha.trans hab
  have hpc : 0 < 1 - p := sub_pos.mpr hp'
  positivity

theorem monomialMaximizer_mem {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) :
    a < monomialMaximizer a b p ∧ monomialMaximizer a b p < b := by
  have hb := ha.trans hab
  have hd := monomial_denominator_pos ha hab hp hp'
  unfold monomialMaximizer
  constructor
  · apply (lt_div_iff hd).2
    nlinarith only [mul_pos ha (mul_pos (sub_pos.mpr hab) hp)]
  · apply (div_lt_iff hd).2
    nlinarith only [mul_pos hb (mul_pos (sub_pos.mpr hab) (sub_pos.mpr hp'))]

/-- The two endpoint factors at the maximizing reciprocal step. -/
theorem monomialMaximizer_factors {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) :
    (monomialMaximizer a b p - a) / monomialMaximizer a b p = (b - a) * p / b ∧
    (b - monomialMaximizer a b p) / monomialMaximizer a b p = (b - a) * (1 - p) / a := by
  have hb := ha.trans hab
  have hd := monomial_denominator_pos ha hab hp hp'
  unfold monomialMaximizer
  constructor <;> field_simp <;> ring

/-- Uniform upper bound, obtained from weighted AM-GM with the exact maximizing weights. -/
theorem monomialMultiplier_le_maximum {a b p τ : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) (hτa : a ≤ τ) (hτb : τ ≤ b) :
    monomialMultiplier a b p τ ≤ monomialMaximum a b p := by
  have hb : 0 < b := ha.trans hab
  have hτ : 0 < τ := ha.trans_le hτa
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hpc : 0 < 1 - p := sub_pos.mpr hp'
  have hx : 0 < (b - a) * p / b := div_pos (mul_pos hgap hp) hb
  have hy : 0 < (b - a) * (1 - p) / a := div_pos (mul_pos hgap hpc) ha
  have h := geometricProduct_tangent hp.le hp'.le hx hy
    (div_nonneg (sub_nonneg.mpr hτa) hτ.le) (div_nonneg (sub_nonneg.mpr hτb) hτ.le)
  have hid : p * (((τ - a) / τ) / ((b - a) * p / b)) +
      (1 - p) * (((b - τ) / τ) / ((b - a) * (1 - p) / a)) = 1 := by
    field_simp
    <;> ring
  rw [hid, mul_one] at h
  exact h

/-- The bound is attained at an interior reciprocal step. -/
theorem monomialMultiplier_at_maximizer {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) :
    monomialMultiplier a b p (monomialMaximizer a b p) = monomialMaximum a b p := by
  obtain ⟨hx, hy⟩ := monomialMaximizer_factors ha hab hp hp'
  unfold monomialMultiplier monomialMaximum
  rw [hx, hy]

/-- A closed-form expression for the worst one-step multiplier. -/
theorem monomialMaximum_closed_form {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) :
    monomialMaximum a b p =
      (b - a) * (p ^ p * (1 - p) ^ (1 - p)) / (b ^ p * a ^ (1 - p)) := by
  have hb : 0 < b := ha.trans hab
  have hg : 0 < b - a := sub_pos.mpr hab
  have hpc : 0 < 1 - p := sub_pos.mpr hp'
  unfold monomialMaximum geometricProduct
  rw [Real.div_rpow (mul_nonneg hg.le hp.le) hb.le,
      Real.div_rpow (mul_nonneg hg.le hpc.le) ha.le,
      Real.mul_rpow hg.le hp.le, Real.mul_rpow hg.le hpc.le]
  have hpow : (b - a) ^ p * (b - a) ^ (1 - p) = b - a := by
    rw [← Real.rpow_add hg]
    convert Real.rpow_one (b-a) using 1 <;> congr 1 <;> ring
  calc
    (b-a) ^ p * p ^ p / b ^ p * ((b-a) ^ (1-p) * (1-p) ^ (1-p) / a ^ (1-p)) =
      ((b-a)^p * (b-a)^(1-p)) * (p^p * (1-p)^(1-p)) / (b^p * a^(1-p)) := by ring
    _ = _ := by rw [hpow]


/-- Strictness in the affine AM-GM tangent bound. -/
theorem geometricProduct_tangent_strict {p x y u v : ℝ} (hp : 0 < p) (hp' : p < 1)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 < u) (hv : 0 < v)
    (hne : u / x ≠ v / y) :
    geometricProduct p u v < geometricProduct p x y * (p * (u / x) + (1 - p) * (v / y)) := by
  have h := weighted_geom_lt_arith (div_pos hu hx) (div_pos hv hy) hp hp' hne
  have heq : geometricProduct p u v =
      geometricProduct p x y * geometricProduct p (u / x) (v / y) := by
    rw [← geometricProduct_mul hx.le hy.le (div_nonneg hu.le hx.le) (div_nonneg hv.le hy.le)]
    congr 1 <;> field_simp
  rw [heq]
  exact mul_lt_mul_of_pos_left h (geometricProduct_pos hx hy)

/-- The maximizing reciprocal step is unique. -/
theorem monomialMultiplier_eq_maximum_iff {a b p τ : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) (hτa : a ≤ τ) (hτb : τ ≤ b) :
    monomialMultiplier a b p τ = monomialMaximum a b p ↔ τ = monomialMaximizer a b p := by
  have hb : 0 < b := ha.trans hab
  have hτ : 0 < τ := ha.trans_le hτa
  have hg : 0 < b - a := sub_pos.mpr hab
  have hpc : 0 < 1 - p := sub_pos.mpr hp'
  have hx : 0 < (b - a) * p / b := div_pos (mul_pos hg hp) hb
  have hy : 0 < (b - a) * (1 - p) / a := div_pos (mul_pos hg hpc) ha
  have hG : 0 < monomialMaximum a b p := geometricProduct_pos hx hy
  constructor
  · intro heq
    by_cases htleft : τ = a
    · subst τ
      simp only [monomialMultiplier, geometricProduct, sub_self, zero_div,
        Real.zero_rpow hp.ne', zero_mul] at heq
      linarith only [hG, heq]
    by_cases htright : τ = b
    · subst τ
      simp only [monomialMultiplier, geometricProduct, sub_self, zero_div,
        Real.zero_rpow hpc.ne', mul_zero] at heq
      linarith only [hG, heq]
    have hl : a < τ := lt_of_le_of_ne hτa (Ne.symm htleft)
    have hr : τ < b := lt_of_le_of_ne hτb htright
    have hid : p * (((τ - a) / τ) / ((b - a) * p / b)) +
        (1 - p) * (((b - τ) / τ) / ((b - a) * (1 - p) / a)) = 1 := by
      field_simp
      <;> ring
    have hxy : ((τ - a) / τ) / ((b - a) * p / b) =
        ((b - τ) / τ) / ((b - a) * (1 - p) / a) := by
      by_contra hne
      have hstrict := geometricProduct_tangent_strict hp hp' hx hy
        (div_pos (sub_pos.mpr hl) hτ) (div_pos (sub_pos.mpr hr) hτ) hne
      rw [hid, mul_one] at hstrict
      exact (ne_of_lt hstrict) heq
    have hdiff :
        ((τ - a) / τ) / ((b - a) * p / b) - ((b - τ) / τ) / ((b - a) * (1 - p) / a) =
        (τ * (b * (1 - p) + a * p) - a * b) / (τ * (b - a) * p * (1 - p)) := by
      field_simp
      <;> ring
    rw [hxy, sub_self] at hdiff
    have hden : τ * (b - a) * p * (1 - p) ≠ 0 := (mul_pos (mul_pos (mul_pos hτ hg) hp) hpc).ne'
    have hnum : τ * (b * (1 - p) + a * p) - a * b = 0 :=
      (div_eq_zero_iff).mp hdiff.symm |>.resolve_right hden
    unfold monomialMaximizer
    apply (eq_div_iff (monomial_denominator_pos ha hab hp hp').ne').2
    linarith only [hnum]
  · intro hτeq
    rw [hτeq]
    exact monomialMultiplier_at_maximizer ha hab hp hp'

/-- Every endpoint monomial has the same value at the spectral midpoint. -/
theorem monomialMultiplier_midpoint {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 ≤ p) (hp' : p ≤ 1) :
    monomialMultiplier a b p ((a + b) / 2) = endpointRate a b := by
  have hab0 : a + b ≠ 0 := ne_of_gt (by linarith only [ha, hab])
  have hba0 : b + a ≠ 0 := ne_of_gt (by linarith only [ha, hab])
  have hx : (((a+b)/2) - a) / ((a+b)/2) = endpointRate a b := by
    unfold endpointRate
    field_simp
    <;> ring
  have hy : (b - ((a+b)/2)) / ((a+b)/2) = endpointRate a b := by
    unfold endpointRate
    field_simp
    <;> ring
  unfold monomialMultiplier
  rw [hx, hy, geometricProduct_self hp hp' (endpointRate_pos ha hab).le]

/-- The maximizing reciprocal step is the midpoint precisely at the distinguished exponent. -/
theorem monomialMaximizer_eq_midpoint_iff {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) :
    monomialMaximizer a b p = (a + b) / 2 ↔ p = endpointTheta a b := by
  have hd := monomial_denominator_pos ha hab hp hp'
  have hsum : a + b ≠ 0 := ne_of_gt (by linarith only [ha, hab])
  constructor
  · intro heq
    unfold monomialMaximizer at heq
    have hc := (div_eq_div_iff hd.ne' (by norm_num : (2:ℝ) ≠ 0)).mp heq
    have hprod : (b-a) * ((a+b)*p - b) = 0 := by
      linear_combination hc
    have hpnum : (a+b)*p - b = 0 := (mul_eq_zero.mp hprod).resolve_left (sub_pos.mpr hab).ne'
    unfold endpointTheta
    apply (eq_div_iff hsum).2
    linarith only [hpnum]
  · intro hpval
    rw [hpval]
    unfold monomialMaximizer endpointTheta
    have hb : 0 < b := ha.trans hab
    field_simp [ha.ne', hb.ne', hsum]
    <;> ring

/-- No exponent improves on the critical endpoint rate. -/
theorem endpointRate_le_monomialMaximum {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) : endpointRate a b ≤ monomialMaximum a b p := by
  have h := monomialMultiplier_le_maximum ha hab hp hp'
    (by linarith only [hab] : a ≤ (a+b)/2) (by linarith only [hab] : (a+b)/2 ≤ b)
  rw [monomialMultiplier_midpoint ha hab hp.le hp'.le] at h
  exact h

/-- The distinguished endpoint exponents are the unique minimax choice. -/
theorem monomialMaximum_eq_rate_iff {a b p : ℝ} (ha : 0 < a) (hab : a < b)
    (hp : 0 < p) (hp' : p < 1) :
    monomialMaximum a b p = endpointRate a b ↔ p = endpointTheta a b := by
  constructor
  · intro heq
    have hmid : monomialMultiplier a b p ((a+b)/2) = monomialMaximum a b p :=
      (monomialMultiplier_midpoint ha hab hp.le hp'.le).trans heq.symm
    have hτ := (monomialMultiplier_eq_maximum_iff ha hab hp hp'
      (by linarith only [hab] : a ≤ (a+b)/2) (by linarith only [hab] : (a+b)/2 ≤ b)).mp hmid
    exact (monomialMaximizer_eq_midpoint_iff ha hab hp hp').mp hτ.symm
  · intro hpval
    have hτ := (monomialMaximizer_eq_midpoint_iff ha hab hp hp').mpr hpval
    rw [← monomialMultiplier_at_maximizer ha hab hp hp', hτ,
      monomialMultiplier_midpoint ha hab hp.le hp'.le]

end BB
