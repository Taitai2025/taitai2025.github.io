import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

/-!
# Polynomial identities for the sharp nonlinear examples

This file proves actual derivative and vanishing assertions about the quartic
perturbation in Section 6. It does not claim the nonlinear convergence theorem.
-/

noncomputable section

namespace BB.Nonlinear

/-- Quartic perturbation used in the nonquadratic sharpness examples. -/
def quartic (r u v : ℝ) : ℝ := (v ^ 2 - r ^ 2 * u ^ 2) ^ 2

/-- The complete polynomial objective in the sharpness construction. -/
def sharpObjective (m M η r u v : ℝ) : ℝ :=
  (m * u ^ 2 + M * v ^ 2) / 2 + η * quartic r u v

/-- Actual derivative of the quartic with respect to its first coordinate. -/
theorem quartic_hasDerivAt_first (r u v : ℝ) :
    HasDerivAt (fun z : ℝ => quartic r z v)
      (-4 * r ^ 2 * u * (v ^ 2 - r ^ 2 * u ^ 2)) u := by
  have h := ((hasDerivAt_const u (v ^ 2)).sub
    (((hasDerivAt_id u).pow 2).const_mul (r ^ 2))).pow 2
  convert h using 1
  simp [quartic]
  ring

/-- Actual derivative of the quartic with respect to its second coordinate. -/
theorem quartic_hasDerivAt_second (r u v : ℝ) :
    HasDerivAt (fun z : ℝ => quartic r u z)
      (4 * v * (v ^ 2 - r ^ 2 * u ^ 2)) v := by
  have h := (((hasDerivAt_id v).pow 2).sub_const (r ^ 2 * u ^ 2)).pow 2
  convert h using 1
  simp [quartic]
  ring

/-- First partial derivative of the complete nonquadratic objective. -/
theorem sharpObjective_hasDerivAt_first (m M η r u v : ℝ) :
    HasDerivAt (fun z : ℝ => sharpObjective m M η r z v)
      (m * u - 4 * η * r ^ 2 * u * (v ^ 2 - r ^ 2 * u ^ 2)) u := by
  have hq := ((((hasDerivAt_id u).pow 2).const_mul m).add_const (M * v ^ 2)).div_const 2
  have hp := (quartic_hasDerivAt_first r u v).const_mul η
  convert hq.add hp using 1
  simp [sharpObjective]
  ring

/-- Second partial derivative of the complete nonquadratic objective. -/
theorem sharpObjective_hasDerivAt_second (m M η r u v : ℝ) :
    HasDerivAt (fun z : ℝ => sharpObjective m M η r u z)
      (M * v + 4 * η * v * (v ^ 2 - r ^ 2 * u ^ 2)) v := by
  have hq := ((((hasDerivAt_id v).pow 2).const_mul M).const_add (m * u ^ 2)).div_const 2
  have hp := (quartic_hasDerivAt_second r u v).const_mul η
  convert hq.add hp using 1
  simp [sharpObjective]
  ring

/-- The perturbation and both partial derivatives vanish on the two lines. -/
theorem quartic_vanishes_on_lines (r u v : ℝ) (hline : v ^ 2 = r ^ 2 * u ^ 2) :
    quartic r u v = 0 ∧
      HasDerivAt (fun z : ℝ => quartic r z v) 0 u ∧
      HasDerivAt (fun z : ℝ => quartic r u z) 0 v := by
  refine ⟨by simp [quartic, hline], ?_, ?_⟩
  · simpa only [hline, sub_self, mul_zero] using quartic_hasDerivAt_first r u v
  · simpa only [hline, sub_self, mul_zero] using quartic_hasDerivAt_second r u v

/-- The objective and its partial derivatives equal the quadratic ones on the lines. -/
theorem sharpObjective_matches_quadratic_on_lines (m M η r u v : ℝ)
    (hline : v ^ 2 = r ^ 2 * u ^ 2) :
    sharpObjective m M η r u v = (m * u ^ 2 + M * v ^ 2) / 2 ∧
      HasDerivAt (fun z : ℝ => sharpObjective m M η r z v) (m * u) u ∧
      HasDerivAt (fun z : ℝ => sharpObjective m M η r u z) (M * v) v := by
  refine ⟨by simp [sharpObjective, quartic, hline], ?_, ?_⟩
  · simpa only [hline, sub_self, mul_zero, sub_zero] using
      sharpObjective_hasDerivAt_first m M η r u v
  · simpa only [hline, sub_self, mul_zero, add_zero] using
      sharpObjective_hasDerivAt_second m M η r u v

/-- The global lower bound proving strict positivity away from the origin. -/
theorem sharpObjective_lower_bound (m M η r u v : ℝ)
    (hmM : m ≤ M) (hη : 0 ≤ η) :
    m / 2 * (u ^ 2 + v ^ 2) ≤ sharpObjective m M η r u v := by
  have h1 := mul_nonneg (sub_nonneg.mpr hmM) (sq_nonneg v)
  have h2 := mul_nonneg hη (sq_nonneg (v ^ 2 - r ^ 2 * u ^ 2))
  dsimp [sharpObjective, quartic]
  nlinarith only [h1, h2]

/-- Exactly the origin has objective value zero, when m>0 and η≥0. -/
theorem sharpObjective_eq_zero_iff (m M η r u v : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hη : 0 ≤ η) :
    sharpObjective m M η r u v = 0 ↔ u = 0 ∧ v = 0 := by
  constructor
  · intro h
    have hb := sharpObjective_lower_bound m M η r u v hmM hη
    have hs : u ^ 2 + v ^ 2 = 0 := by
      have hnonneg : 0 ≤ u ^ 2 + v ^ 2 := add_nonneg (sq_nonneg u) (sq_nonneg v)
      have hmul : m / 2 * (u ^ 2 + v ^ 2) ≤ 0 := by simpa only [h] using hb
      have hle : u ^ 2 + v ^ 2 ≤ 0 := (mul_le_mul_left (by linarith : 0 < m / 2)).mp (by simpa using hmul)
      exact le_antisymm hle hnonneg
    have hu : u ^ 2 = 0 := by nlinarith only [hs, sq_nonneg v, sq_nonneg u]
    have hv : v ^ 2 = 0 := by nlinarith only [hs, sq_nonneg v, sq_nonneg u]
    exact ⟨sq_eq_zero_iff.mp hu, sq_eq_zero_iff.mp hv⟩
  · rintro ⟨rfl, rfl⟩
    simp [sharpObjective, quartic]

/-- No univariate quadratic can equal the restriction u=0 when η>0. -/
theorem sharpObjective_nonquadratic (m M η r : ℝ) (hη : 0 < η) :
    ¬ ∃ a b c : ℝ, ∀ v : ℝ,
      sharpObjective m M η r 0 v = a * v ^ 2 + b * v + c := by
  rintro ⟨a, b, c, h⟩
  have h0 := h 0
  have h1 := h 1
  have hn1 := h (-1)
  have h2 := h 2
  norm_num [sharpObjective, quartic] at h0 h1 hn1 h2
  linarith only [h0, h1, hn1, h2, hη]

/-- BB1 for a diagonal quadratic, written in its two scalar coordinates. -/
def diagonalBB1 (m M x y : ℝ) : ℝ := (x ^ 2 + y ^ 2) / (m * x ^ 2 + M * y ^ 2)

/-- BB2 for a diagonal quadratic, written in its two scalar coordinates. -/
def diagonalBB2 (m M x y : ℝ) : ℝ :=
  (m * x ^ 2 + M * y ^ 2) / (m ^ 2 * x ^ 2 + M ^ 2 * y ^ 2)

/-- Equal secant energies give the exact BB1 endpoint step. -/
theorem balanced_diagonal_bb1 (m M x y : ℝ) (hx : x ≠ 0) (hbalance : x ^ 2 = y ^ 2) :
    diagonalBB1 m M x y = 2 / (m + M) := by
  have hnum : x ^ 2 + y ^ 2 = 2 * x ^ 2 := by rw [← hbalance]; ring
  have hden : m * x ^ 2 + M * y ^ 2 = (m + M) * x ^ 2 := by rw [← hbalance]; ring
  rw [diagonalBB1, hnum, hden, mul_div_mul_right _ _ (pow_ne_zero 2 hx)]

/-- Equal weighted secant energies give the exact BB2 endpoint step. -/
theorem balanced_diagonal_bb2 (m M x y : ℝ) (hm : m ≠ 0) (hx : x ≠ 0)
    (hbalance : m * x ^ 2 = M * y ^ 2) :
    diagonalBB2 m M x y = 2 / (m + M) := by
  have hnum : m * x ^ 2 + M * y ^ 2 = 2 * (m * x ^ 2) := by linarith only [hbalance]
  have hden : m ^ 2 * x ^ 2 + M ^ 2 * y ^ 2 = (m + M) * (m * x ^ 2) := by
    have h := congrArg (fun z : ℝ => M * z) hbalance
    dsimp only at h
    nlinarith only [h]
  rw [diagonalBB2, hnum, hden,
    mul_div_mul_right _ _ (mul_ne_zero hm (pow_ne_zero 2 hx))]

/-- The two endpoint coordinate multipliers have equal magnitude and opposite sign. -/
theorem endpoint_update_multipliers (m M : ℝ) (h : m + M ≠ 0) :
    1 - (2 / (m + M)) * m = (M - m) / (M + m) ∧
    1 - (2 / (m + M)) * M = -(M - m) / (M + m) := by
  have h' : M + m ≠ 0 := by simpa [add_comm] using h
  constructor <;> field_simp [h, h'] <;> ring

/-- The BB1 sharp-example incoming secant has the required balance. -/
theorem endpoint_secant_bb1 (m M u v α : ℝ)
    (hm : m ≠ 0) (hu : u ≠ 0) (hα : α ≠ 0)
    (hbalance : m ^ 2 * u ^ 2 = M ^ 2 * v ^ 2) :
    diagonalBB1 m M (-α * m * u) (-α * M * v) = 2 / (m + M) := by
  apply balanced_diagonal_bb1
  · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hα) hm) hu
  · have h := congrArg (fun z : ℝ => α ^ 2 * z) hbalance
    dsimp only at h
    nlinarith only [h]

/-- The BB2 sharp-example incoming secant has the required weighted balance. -/
theorem endpoint_secant_bb2 (m M u v α : ℝ)
    (hm : m ≠ 0) (hu : u ≠ 0) (hα : α ≠ 0)
    (hbalance : m ^ 3 * u ^ 2 = M ^ 3 * v ^ 2) :
    diagonalBB2 m M (-α * m * u) (-α * M * v) = 2 / (m + M) := by
  apply balanced_diagonal_bb2 _ _ _ _ hm
  · exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hα) hm) hu
  · have h := congrArg (fun z : ℝ => α ^ 2 * z) hbalance
    dsimp only at h
    nlinarith only [h]

/-- The two-line equation is preserved by the endpoint update. -/
theorem two_lines_invariant (r u v c : ℝ) (hline : v ^ 2 = r ^ 2 * u ^ 2) :
    (-c * v) ^ 2 = r ^ 2 * (c * u) ^ 2 := by
  have h := congrArg (fun z : ℝ => c ^ 2 * z) hline
  dsimp only at h
  nlinarith only [h]

/-- Squared Euclidean norm contracts by exactly c² in one endpoint update. -/
theorem endpoint_squared_norm (u v c : ℝ) :
    (c * u) ^ 2 + (-c * v) ^ 2 = c ^ 2 * (u ^ 2 + v ^ 2) := by ring

/-- The quadratic objective contracts by c² on every invariant-line step. -/
theorem sharpObjective_exact_step (m M η r u v c : ℝ)
    (hline : v ^ 2 = r ^ 2 * u ^ 2) :
    sharpObjective m M η r (c * u) (-c * v) = c ^ 2 * sharpObjective m M η r u v := by
  rw [(sharpObjective_matches_quadratic_on_lines m M η r _ _ (two_lines_invariant r u v c hline)).1,
    (sharpObjective_matches_quadratic_on_lines m M η r u v hline).1]
  ring

end BB.Nonlinear
