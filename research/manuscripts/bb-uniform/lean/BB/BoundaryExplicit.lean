import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section
namespace BB.BoundaryExplicit

/-- The explicit boundary-comparison horizon from the manuscript. -/
def length (B K c r : ℝ) : ℕ :=
  max 3 (1+Nat.ceil (Real.log (2*B*K/c)/(-Real.log r)))

theorem length_ge_three (B K c r : ℝ) : 3 ≤ length B K c r := le_max_left _ _

/-- The natural ceiling is valid even when its logarithmic argument is negative. -/
theorem logarithmic_length_bound (B K c r : ℝ) :
    Real.log (2*B*K/c)/(-Real.log r) ≤ (length B K c r-1 : ℕ) := by
  have hceil : Nat.ceil (Real.log (2*B*K/c)/(-Real.log r)) ≤ length B K c r-1 := by
    have hh := le_max_right 3 (1+Nat.ceil (Real.log (2*B*K/c)/(-Real.log r)))
    unfold length
    omega
  exact (Nat.le_ceil _).trans (by exact_mod_cast hceil)

/-- The manuscript's displayed logarithm-ceiling choice really makes the
rescaled boundary term at most one half. No extra logarithmic positivity
assumption is required. -/
theorem boundary_length_half {B K c r : ℝ}
    (hB : 0 < B) (hK : 0 < K) (hc : 0 < c) (hr : 0 < r) (hrone : r < 1) :
    (B/c)*K*r^(length B K c r-1) ≤ 1/2 := by
  have hlogr : Real.log r < 0 := Real.log_neg hr hrone
  have hlogden : 0 < -Real.log r := neg_pos.mpr hlogr
  have hlen := (div_le_iff hlogden).mp (logarithmic_length_bound B K c r)
  have hexponent : ((length B K c r-1 : ℕ) : ℝ)*Real.log r ≤ -Real.log (2*B*K/c) := by
    nlinarith only [hlen]
  have hratio : 0 < 2*B*K/c := div_pos (mul_pos (mul_pos (by norm_num) hB) hK) hc
  have hpow : r^(length B K c r-1) ≤ c/(2*B*K) := by
    calc
      r^(length B K c r-1) =
          Real.exp (((length B K c r-1 : ℕ) : ℝ)*Real.log r) := by
        rw [Real.exp_nat_mul,Real.exp_log hr]
      _ ≤ Real.exp (-Real.log (2*B*K/c)) := Real.exp_le_exp.mpr hexponent
      _ = c/(2*B*K) := by rw [Real.exp_neg,Real.exp_log hratio]; field_simp
  calc
    (B/c)*K*r^(length B K c r-1) ≤ (B/c)*K*(c/(2*B*K)) :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (div_nonneg hB.le hc.le) hK.le)
    _ = 1/2 := by field_simp; ring

end BB.BoundaryExplicit
