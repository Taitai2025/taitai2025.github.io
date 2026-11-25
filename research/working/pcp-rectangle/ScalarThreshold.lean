import Mathlib

/-!
Scalar fragments for the static-rectangle PCP note.
These theorems do NOT formalize nuclear norms, matrix subdifferentials,
dual-certificate necessity, or the full bright/dark matrix theorem.
-/
namespace RPCAStaticPatch

theorem price_squared_equiv {a b lam : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 ≤ lam) :
    lam * Real.sqrt (a * b) ≤ 1 ↔ lam ^ 2 * (a * b) ≤ 1 := by
  have hnonneg : 0 ≤ lam * Real.sqrt (a * b) :=
    mul_nonneg hlam (Real.sqrt_nonneg (a * b))
  have heq : (lam * Real.sqrt (a * b)) ^ 2 = lam ^ 2 * (a * b) := by
    rw [mul_pow, Real.sq_sqrt (mul_nonneg ha hb)]
  constructor
  · intro h
    have hp : 0 ≤ (1 - lam * Real.sqrt (a * b)) *
        (1 + lam * Real.sqrt (a * b)) :=
      mul_nonneg (sub_nonneg.mpr h) (by linarith)
    nlinarith [heq]
  · intro h
    nlinarith [heq, sq_nonneg (lam * Real.sqrt (a * b) - 1)]

theorem area_budget_equiv {a b lam : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hlam : 0 < lam) :
    lam * Real.sqrt (a * b) ≤ 1 ↔ a * b ≤ 1 / lam ^ 2 := by
  rw [price_squared_equiv ha hb (le_of_lt hlam)]
  rw [le_div_iff (sq_pos_of_pos hlam)]
  rw [mul_comm (a * b) (lam ^ 2)]

theorem dark_half_obstruction {lam ell T b : ℝ}
    (hlam : 0 < lam) (hell : 0 < ell) (hT : 0 < T)
    (hhalf : T ≤ 2 * b) :
    ¬ (ell * T ≤ lam * (T - 2 * b)) := by
  have hn : T - 2 * b ≤ 0 := by linarith
  have hp : 0 < ell * T := mul_pos hell hT
  have hq : lam * (T - 2 * b) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hlam) hn
  linarith

end RPCAStaticPatch

#print axioms RPCAStaticPatch.price_squared_equiv
#print axioms RPCAStaticPatch.area_budget_equiv
#print axioms RPCAStaticPatch.dark_half_obstruction
