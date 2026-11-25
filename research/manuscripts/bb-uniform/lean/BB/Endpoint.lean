import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

noncomputable section

namespace BB

open Real

/-- The critical rate of the two extreme eigenvalues. -/
def endpointRate (a b : ℝ) : ℝ := (b - a) / (b + a)

/-- The endpoint exponent attached to the lower eigenvalue. -/
def endpointTheta (a b : ℝ) : ℝ := b / (a + b)

/-- The square-root multiplier of the endpoint product. -/
def endpointMultiplier (a b τ : ℝ) : ℝ :=
  ((τ - a) / τ) ^ endpointTheta a b *
  ((b - τ) / τ) ^ (1 - endpointTheta a b)


theorem endpointRate_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < endpointRate a b := by
  unfold endpointRate
  exact div_pos (sub_pos.mpr hab) (by linarith)

theorem endpointRate_lt_one {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    endpointRate a b < 1 := by
  unfold endpointRate
  apply (div_lt_one (by linarith : 0 < b + a)).2
  linarith

theorem endpointTheta_pos {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    0 < endpointTheta a b := by
  unfold endpointTheta
  exact div_pos (by linarith) (by linarith)

theorem endpointTheta_lt_one {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    endpointTheta a b < 1 := by
  unfold endpointTheta
  apply (div_lt_one (by linarith : 0 < a + b)).2
  linarith

theorem endpoint_complement {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    1 - endpointTheta a b = a / (a + b) := by
  unfold endpointTheta
  have h : a + b ≠ 0 := ne_of_gt (by linarith)
  field_simp
  <;> ring

/-- The weighted arithmetic mean of the two endpoint multipliers is constant. -/
theorem endpoint_arithmetic_identity {a b τ : ℝ} (ha : 0 < a) (hab : a < b)
    (hτ : a ≤ τ) :
    endpointTheta a b * ((τ - a) / τ) +
      (1 - endpointTheta a b) * ((b - τ) / τ) = endpointRate a b := by
  unfold endpointTheta endpointRate
  have hτ0 : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hτ)
  have hab0 : a + b ≠ 0 := ne_of_gt (by linarith)
  have hba0 : b + a ≠ 0 := ne_of_gt (by linarith)
  field_simp
  <;> ring

/-- The sharp scalar endpoint inequality, including both terminal endpoints. -/
theorem endpointMultiplier_le {a b τ : ℝ} (ha : 0 < a) (hab : a < b)
    (hτa : a ≤ τ) (hτb : τ ≤ b) :
    endpointMultiplier a b τ ≤ endpointRate a b := by
  have hθ := endpointTheta_pos ha hab
  have hθ' := endpointTheta_lt_one ha hab
  have hτ : 0 < τ := lt_of_lt_of_le ha hτa
  have h := Real.geom_mean_le_arith_mean2_weighted (le_of_lt hθ)
    (by linarith : 0 ≤ 1 - endpointTheta a b)
    (div_nonneg (sub_nonneg.mpr hτa) hτ.le)
    (div_nonneg (sub_nonneg.mpr hτb) hτ.le)
    (by ring : endpointTheta a b + (1 - endpointTheta a b) = 1)
  exact h.trans_eq (endpoint_arithmetic_identity ha hab hτa)

/-- Strict weighted AM-GM for two positive, unequal numbers. -/
theorem weighted_geom_lt_arith {x y θ : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hθ : 0 < θ) (hθ' : θ < 1) (hne : x ≠ y) :
    x ^ θ * y ^ (1 - θ) < θ * x + (1 - θ) * y := by
  have h := strictConcaveOn_log_Ioi.2 hx hy hne hθ
    (by linarith : 0 < 1 - θ) (by ring : θ + (1 - θ) = 1)
  simp only [smul_eq_mul] at h
  have hθc : 0 < 1 - θ := by linarith
  have hm : 0 < θ * x + (1 - θ) * y := by positivity
  calc
    x ^ θ * y ^ (1 - θ) = Real.exp (θ * Real.log x + (1 - θ) * Real.log y) := by
      rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hy, ← Real.exp_add]
      congr 1
      ring
    _ < Real.exp (Real.log (θ * x + (1 - θ) * y)) := Real.exp_lt_exp.mpr h
    _ = θ * x + (1 - θ) * y := Real.exp_log hm


/-- Equality in the endpoint inequality occurs exactly at the midpoint. -/
theorem endpointMultiplier_eq_iff {a b τ : ℝ} (ha : 0 < a) (hab : a < b)
    (hτa : a ≤ τ) (hτb : τ ≤ b) :
    endpointMultiplier a b τ = endpointRate a b ↔ τ = (a + b) / 2 := by
  have hθ := endpointTheta_pos ha hab
  have hθ' := endpointTheta_lt_one ha hab
  have hc := endpointRate_pos ha hab
  have hτ : 0 < τ := lt_of_lt_of_le ha hτa
  have hθc : 0 < 1 - endpointTheta a b := by linarith
  constructor
  · intro heq
    by_cases hleft : τ = a
    · subst τ
      simp only [endpointMultiplier, sub_self, zero_div, Real.zero_rpow hθ.ne', zero_mul] at heq
      linarith
    by_cases hright : τ = b
    · subst τ
      simp only [endpointMultiplier, sub_self, zero_div, Real.zero_rpow hθc.ne', mul_zero] at heq
      linarith
    have hτa' : a < τ := lt_of_le_of_ne hτa (Ne.symm hleft)
    have hτb' : τ < b := lt_of_le_of_ne hτb hright
    have hxy : (τ - a) / τ = (b - τ) / τ := by
      by_contra hne
      have hstrict := weighted_geom_lt_arith
        (div_pos (sub_pos.mpr hτa') hτ) (div_pos (sub_pos.mpr hτb') hτ)
        hθ hθ' hne
      rw [endpoint_arithmetic_identity ha hab hτa] at hstrict
      exact (ne_of_lt hstrict) heq
    have hnum : τ - a = b - τ := by
      exact (div_left_inj' hτ.ne').mp hxy
    linarith
  · intro hmid
    have hx : (τ - a) / τ = endpointRate a b := by
      rw [hmid]
      unfold endpointRate
      have hab0 : a + b ≠ 0 := ne_of_gt (by linarith)
      have hba0 : b + a ≠ 0 := ne_of_gt (by linarith)
      field_simp
      <;> ring
    have hy : (b - τ) / τ = endpointRate a b := by
      rw [hmid]
      unfold endpointRate
      have hab0 : a + b ≠ 0 := ne_of_gt (by linarith)
      have hba0 : b + a ≠ 0 := ne_of_gt (by linarith)
      field_simp
      <;> ring
    unfold endpointMultiplier
    rw [hx, hy, ← Real.rpow_add hc]
    convert Real.rpow_one (endpointRate a b) using 1 <;> congr 1 <;> ring


/-- A weighted geometric mean of two nonnegative endpoint sizes. -/
def geometricProduct (θ x y : ℝ) : ℝ := x ^ θ * y ^ (1 - θ)

theorem geometricProduct_nonneg {θ x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ geometricProduct θ x y :=
  mul_nonneg (Real.rpow_nonneg hx _) (Real.rpow_nonneg hy _)

theorem geometricProduct_pos {θ x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < geometricProduct θ x y :=
  mul_pos (Real.rpow_pos_of_pos hx _) (Real.rpow_pos_of_pos hy _)

theorem geometricProduct_mul {θ s t x y : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricProduct θ (s * x) (t * y) =
      geometricProduct θ s t * geometricProduct θ x y := by
  unfold geometricProduct
  rw [Real.mul_rpow hs hx, Real.mul_rpow ht hy]
  ring

theorem geometricProduct_self {θ x : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hx : 0 ≤ x) : geometricProduct θ x x = x := by
  unfold geometricProduct
  rw [← Real.rpow_add_of_nonneg hx hθ (sub_nonneg.mpr hθ')]
  convert Real.rpow_one x using 1 <;> congr 1 <;> ring

theorem geometricProduct_homogeneous {θ s x y : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricProduct θ (s * x) (s * y) = s * geometricProduct θ x y := by
  rw [geometricProduct_mul hs hs hx hy, geometricProduct_self hθ hθ' hs]

theorem geometricProduct_mono {θ x y x' y' : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxx' : x ≤ x') (hyy' : y ≤ y') :
    geometricProduct θ x y ≤ geometricProduct θ x' y' := by
  apply mul_le_mul
  · exact Real.rpow_le_rpow hx hxx' hθ
  · exact Real.rpow_le_rpow hy hyy' (sub_nonneg.mpr hθ')
  · exact Real.rpow_nonneg hy _
  · exact Real.rpow_nonneg (hx.trans hxx') _

theorem geometricProduct_le {θ x y r : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxr : x ≤ r) (hyr : y ≤ r) : geometricProduct θ x y ≤ r := by
  exact (geometricProduct_mono hθ hθ' hx hy hxr hyr).trans_eq
    (geometricProduct_self hθ hθ' (hx.trans hxr))

theorem min_le_geometricProduct {θ x y : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    min x y ≤ geometricProduct θ x y := by
  have hm : 0 ≤ min x y := le_min hx hy
  calc
    min x y = geometricProduct θ (min x y) (min x y) :=
      (geometricProduct_self hθ hθ' hm).symm
    _ ≤ geometricProduct θ x y :=
      geometricProduct_mono hθ hθ' hm hm (min_le_left _ _) (min_le_right _ _)

theorem geometricProduct_eq_zero_iff {θ x y : ℝ}
    (hθ : 0 < θ) (hθ' : θ < 1) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricProduct θ x y = 0 ↔ x = 0 ∨ y = 0 := by
  unfold geometricProduct
  rw [mul_eq_zero, Real.rpow_eq_zero hx hθ.ne',
    Real.rpow_eq_zero hy (by linarith : 1 - θ ≠ 0)]

/-- The endpoint product contracts for the actual two scalar component updates. -/
theorem endpointProduct_decay {a b τ x y : ℝ} (ha : 0 < a) (hab : a < b)
    (hτa : a ≤ τ) (hτb : τ ≤ b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricProduct (endpointTheta a b) (((τ - a) / τ) * x) (((b - τ) / τ) * y)
      ≤ endpointRate a b * geometricProduct (endpointTheta a b) x y := by
  have hτ : 0 < τ := lt_of_lt_of_le ha hτa
  rw [geometricProduct_mul (div_nonneg (sub_nonneg.mpr hτa) hτ.le)
    (div_nonneg (sub_nonneg.mpr hτb) hτ.le) hx hy]
  exact mul_le_mul_of_nonneg_right (endpointMultiplier_le ha hab hτa hτb)
    (geometricProduct_nonneg hx hy)

/-- The nonnegative logarithmic defect, defined on interior reciprocal steps. -/
def endpointDefect (a b τ : ℝ) : ℝ :=
  Real.log (endpointRate a b) -
    endpointTheta a b * Real.log ((τ - a) / τ) -
    (1 - endpointTheta a b) * Real.log ((b - τ) / τ)

theorem log_endpointMultiplier {a b τ : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) :
    Real.log (endpointMultiplier a b τ) =
      endpointTheta a b * Real.log ((τ - a) / τ) +
      (1 - endpointTheta a b) * Real.log ((b - τ) / τ) := by
  have hτ : 0 < τ := lt_trans ha hτa
  have hx : 0 < (τ - a) / τ := div_pos (sub_pos.mpr hτa) hτ
  have hy : 0 < (b - τ) / τ := div_pos (sub_pos.mpr hτb) hτ
  unfold endpointMultiplier
  rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hy _).ne',
    Real.log_rpow hx, Real.log_rpow hy]

theorem endpointDefect_eq_log_ratio {a b τ : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) :
    endpointDefect a b τ =
      Real.log (endpointRate a b) - Real.log (endpointMultiplier a b τ) := by
  rw [log_endpointMultiplier ha hτa hτb]
  unfold endpointDefect
  ring

theorem endpointDefect_nonneg {a b τ : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) : 0 ≤ endpointDefect a b τ := by
  have hτ : 0 < τ := lt_trans ha hτa
  have hp : 0 < endpointMultiplier a b τ :=
    geometricProduct_pos (div_pos (sub_pos.mpr hτa) hτ) (div_pos (sub_pos.mpr hτb) hτ)
  rw [endpointDefect_eq_log_ratio ha hτa hτb]
  exact sub_nonneg.mpr (Real.log_le_log hp
    (endpointMultiplier_le ha (lt_trans hτa hτb) hτa.le hτb.le))

theorem endpointMultiplier_defect_identity {a b τ : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) :
    endpointMultiplier a b τ = endpointRate a b * Real.exp (-endpointDefect a b τ) := by
  have hc := endpointRate_pos ha (lt_trans hτa hτb)
  have hτ : 0 < τ := lt_trans ha hτa
  have hp : 0 < endpointMultiplier a b τ :=
    geometricProduct_pos (div_pos (sub_pos.mpr hτa) hτ) (div_pos (sub_pos.mpr hτb) hτ)
  calc
    endpointMultiplier a b τ = Real.exp (Real.log (endpointMultiplier a b τ)) :=
      (Real.exp_log hp).symm
    _ = Real.exp (Real.log (endpointRate a b)) * Real.exp (-endpointDefect a b τ) := by
      rw [← Real.exp_add]
      congr 1
      rw [endpointDefect_eq_log_ratio ha hτa hτb]
      ring
    _ = endpointRate a b * Real.exp (-endpointDefect a b τ) := by
      rw [Real.exp_log hc]

theorem endpointDefect_eq_zero_iff {a b τ : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) :
    endpointDefect a b τ = 0 ↔ τ = (a + b) / 2 := by
  have hab := lt_trans hτa hτb
  constructor
  · intro hD
    have hmul := endpointMultiplier_defect_identity ha hτa hτb
    rw [hD, neg_zero, Real.exp_zero, mul_one] at hmul
    exact (endpointMultiplier_eq_iff ha hab hτa.le hτb.le).mp hmul
  · intro hmid
    rw [endpointDefect_eq_log_ratio ha hτa hτb,
      (endpointMultiplier_eq_iff ha hab hτa.le hτb.le).mpr hmid, sub_self]

/-- Exact dissipation of the squared endpoint product. -/
theorem endpointEnergy_exact {a b τ x y : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (geometricProduct (endpointTheta a b) (((τ - a) / τ) * x) (((b - τ) / τ) * y)) ^ 2 =
      endpointRate a b ^ 2 * Real.exp (-2 * endpointDefect a b τ) *
        geometricProduct (endpointTheta a b) x y ^ 2 := by
  have hτ : 0 < τ := lt_trans ha hτa
  rw [geometricProduct_mul (div_nonneg (sub_nonneg.mpr hτa.le) hτ.le)
    (div_nonneg (sub_nonneg.mpr hτb.le) hτ.le) hx hy]
  change (endpointMultiplier a b τ * _) ^ 2 = _
  rw [endpointMultiplier_defect_identity ha hτa hτb]
  have he : Real.exp (-2 * endpointDefect a b τ) =
      Real.exp (-endpointDefect a b τ) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
  rw [he]
  ring

/-- Iterating an exact dissipation law gives the cumulative defect formula. -/
theorem cumulative_dissipation (E D : ℕ → ℝ) (c : ℝ)
    (hstep : ∀ k, E (k + 1) = c ^ 2 * Real.exp (-2 * D k) * E k) (k : ℕ) :
    E k = c ^ (2 * k) * Real.exp (-2 * ∑ j ∈ Finset.range k, D j) * E 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hstep, ih, Finset.sum_range_succ]
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    rw [show -2 * ((∑ j ∈ Finset.range k, D j) + D k) =
      -2 * (∑ j ∈ Finset.range k, D j) + -2 * D k by ring, Real.exp_add]
    ring


/-- The endpoint contraction written directly in the stepsize variable. -/
theorem endpointProduct_decay_stepsize {a b α x y : ℝ} (ha : 0 < a) (hab : a < b)
    (hαlo : 1 / b ≤ α) (hαhi : α ≤ 1 / a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricProduct (endpointTheta a b) (|1 - α * a| * x) (|1 - α * b| * y) ≤
      endpointRate a b * geometricProduct (endpointTheta a b) x y := by
  have hb : 0 < b := lt_trans ha hab
  have hαa : α * a ≤ 1 := (le_div_iff ha).mp hαhi
  have hαb : 1 ≤ α * b := (div_le_iff hb).mp hαlo
  have hθ := endpointTheta_pos ha hab
  have hθ' := endpointTheta_lt_one ha hab
  have hxmul : |1 - α * a| = 1 - α * a := abs_of_nonneg (sub_nonneg.mpr hαa)
  have hymul : |1 - α * b| = α * b - 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hαb)]
    ring
  rw [hxmul, hymul, geometricProduct_mul (sub_nonneg.mpr hαa) (sub_nonneg.mpr hαb) hx hy]
  have hmean := Real.geom_mean_le_arith_mean2_weighted hθ.le
    (sub_nonneg.mpr hθ'.le) (sub_nonneg.mpr hαa) (sub_nonneg.mpr hαb)
    (by ring : endpointTheta a b + (1 - endpointTheta a b) = 1)
  have hid : endpointTheta a b * (1 - α * a) + (1 - endpointTheta a b) * (α * b - 1) =
      endpointRate a b := by
    unfold endpointTheta endpointRate
    have hab0 : a + b ≠ 0 := ne_of_gt (add_pos ha hb)
    have hba0 : b + a ≠ 0 := ne_of_gt (add_pos hb ha)
    field_simp
    <;> ring
  exact mul_le_mul_of_nonneg_right (hmean.trans_eq hid) (geometricProduct_nonneg hx hy)


/-- Squaring the degree-one product yields the endpoint energy used in the baseline. -/
theorem geometricProduct_square {θ x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    geometricProduct θ x y ^ 2 = x ^ (2 * θ) * y ^ (2 * (1 - θ)) := by
  unfold geometricProduct
  rw [mul_pow]
  have hxpow : (x ^ θ) ^ 2 = x ^ (2 * θ) := by
    rw [← Real.rpow_natCast (x ^ θ) 2, ← Real.rpow_mul hx]
    congr 1
    norm_num
    ring
  have hypow : (y ^ (1 - θ)) ^ 2 = y ^ (2 * (1 - θ)) := by
    rw [← Real.rpow_natCast (y ^ (1 - θ)) 2, ← Real.rpow_mul hy]
    congr 1
    norm_num
    ring
  rw [hxpow, hypow]

/-- With two surviving endpoint components every interior reciprocal step strictly decreases the energy. -/
theorem endpointEnergy_strict {a b τ x y : ℝ} (ha : 0 < a)
    (hτa : a < τ) (hτb : τ < b) (hx : 0 < x) (hy : 0 < y) :
    0 < geometricProduct (endpointTheta a b) (((τ-a)/τ)*x) (((b-τ)/τ)*y) ^ 2 ∧
      geometricProduct (endpointTheta a b) (((τ-a)/τ)*x) (((b-τ)/τ)*y) ^ 2 <
        geometricProduct (endpointTheta a b) x y ^ 2 := by
  have hab : a < b := hτa.trans hτb
  have hτ : 0 < τ := ha.trans hτa
  have hold := geometricProduct_pos (θ := endpointTheta a b) hx hy
  have hnew := geometricProduct_pos (θ := endpointTheta a b)
    (mul_pos (div_pos (sub_pos.mpr hτa) hτ) hx)
    (mul_pos (div_pos (sub_pos.mpr hτb) hτ) hy)
  have hdec := endpointProduct_decay ha hab hτa.le hτb.le hx.le hy.le
  have hc := endpointRate_lt_one ha hab
  have hless : geometricProduct (endpointTheta a b) (((τ-a)/τ)*x) (((b-τ)/τ)*y) <
      geometricProduct (endpointTheta a b) x y :=
    hdec.trans_lt (by simpa only [one_mul] using mul_lt_mul_of_pos_right hc hold)
  exact ⟨sq_pos_of_pos hnew, sq_lt_sq' (by linarith only [hnew, hold]) hless⟩


/-- Cumulative dissipation for scalar endpoint-size trajectories, with no abstract energy-law assumption. -/
theorem endpointEnergy_cumulative {a b : ℝ} (ha : 0 < a)
    (τ x y : ℕ → ℝ) (hτa : ∀ k, a < τ k) (hτb : ∀ k, τ k < b)
    (hx0 : 0 ≤ x 0) (hy0 : 0 ≤ y 0)
    (hxstep : ∀ k, x (k+1) = ((τ k-a)/(τ k)) * x k)
    (hystep : ∀ k, y (k+1) = ((b-τ k)/(τ k)) * y k) (k : ℕ) :
    geometricProduct (endpointTheta a b) (x k) (y k) ^ 2 =
      endpointRate a b ^ (2*k) *
        Real.exp (-2 * ∑ j ∈ Finset.range k, endpointDefect a b (τ j)) *
        geometricProduct (endpointTheta a b) (x 0) (y 0) ^ 2 := by
  have hxy : ∀ k, 0 ≤ x k ∧ 0 ≤ y k := by
    intro k
    induction k with
    | zero => exact ⟨hx0,hy0⟩
    | succ k ih =>
      rw [hxstep, hystep]
      have ht : 0 < τ k := ha.trans (hτa k)
      exact ⟨mul_nonneg (div_nonneg (sub_nonneg.mpr (hτa k).le) ht.le) ih.1,
        mul_nonneg (div_nonneg (sub_nonneg.mpr (hτb k).le) ht.le) ih.2⟩
  apply cumulative_dissipation (fun k => geometricProduct (endpointTheta a b) (x k) (y k) ^ 2)
    (fun k => endpointDefect a b (τ k)) (endpointRate a b) _ k
  intro j
  dsimp only
  rw [hxstep, hystep]
  exact endpointEnergy_exact ha (hτa j) (hτb j) (hxy j).1 (hxy j).2

end BB
