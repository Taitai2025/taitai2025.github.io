import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # The scalar example distinguishing a root factor from an exact uniform bound

This is the literal sequence `n * c^n` used in the introduction.  All results
hold for every positive `c`; hence in particular for `0 < c < 1`.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Introduction
open Filter
open scoped Topology

def polynomialGeometric (c : ℝ) (n : ℕ) : ℝ := (n : ℝ) * c^n

theorem polynomialGeometric_nonnegative {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    0 ≤ polynomialGeometric c n := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hc _)

theorem polynomialGeometric_root {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : n ≠ 0) :
    (polynomialGeometric c n)^(1/(n : ℝ)) = (n : ℝ)^(1/(n : ℝ))*c := by
  rw [polynomialGeometric, Real.mul_rpow (Nat.cast_nonneg _) (pow_nonneg hc.le _)]
  rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
  have hnr : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [mul_one_div_cancel hnr, Real.rpow_one]

theorem polynomialGeometric_root_limit {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ => (polynomialGeometric c n)^(1/(n : ℝ))) atTop (𝓝 c) := by
  have h := (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop).mul_const c
  simp only [one_mul] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact (polynomialGeometric_root hc (by omega : n ≠ 0)).symm

/-- Every proposed exact-factor prefactor fails at some natural index. -/
theorem polynomialGeometric_exceeds_every_prefactor {c : ℝ} (hc : 0 < c) (K : ℝ) :
    ∃ n : ℕ, K*c^n < polynomialGeometric c n := by
  obtain ⟨n, hn⟩ := exists_nat_gt K
  exact ⟨n, mul_lt_mul_of_pos_right hn (pow_pos hc _)⟩

theorem polynomialGeometric_no_uniform_prefactor {c : ℝ} (hc : 0 < c) :
    ¬ ∃ K : ℝ, ∀ n : ℕ, polynomialGeometric c n ≤ K*c^n := by
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := polynomialGeometric_exceeds_every_prefactor hc K
  exact hn.not_le (hK n)

end BB.Introduction
