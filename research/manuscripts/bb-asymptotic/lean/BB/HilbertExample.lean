import BB.Hilbert
import BB.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Polynomial integrals for the continuous-spectrum example

These are the scalar integrals after the affine change of spectral variable
from `[a,b]` to `[-1,1]`. They prove the finite-step norm-square and the symmetry
moment identities. They do not assert an unformalized L2 spectral theorem.
-/

noncomputable section

open MeasureTheory

namespace BB

theorem symmetric_even_power_integral (k : ℕ) :
    (∫ t : ℝ in (-1)..1, t ^ (2 * k)) = 2 / (2 * (k : ℝ) + 1) := by
  rw [integral_pow]
  have hneg : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    simp [pow_add, pow_mul]
  rw [hneg]
  norm_num

theorem symmetric_odd_power_integral (k : ℕ) :
    (∫ t : ℝ in (-1)..1, t ^ (2 * k + 1)) = 0 := by
  rw [integral_pow]
  have hneg : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
    simp [pow_add, pow_mul]
  rw [hneg]
  simp

theorem continuous_spectrum_norm_square (c : ℝ) (k : ℕ) :
    (∫ t : ℝ in (-1)..1, ((-c * t) ^ k) ^ 2) =
      2 * c ^ (2 * k) / (2 * (k : ℝ) + 1) := by
  have hpoint : (fun t : ℝ => ((-c * t) ^ k) ^ 2) =
      (fun t : ℝ => c ^ (2 * k) * t ^ (2 * k)) := by
    funext t
    rw [← pow_mul, Nat.mul_comm k 2, mul_pow]
    simp [pow_mul]
  rw [hpoint, intervalIntegral.integral_const_mul, symmetric_even_power_integral]
  ring

/-- The odd first moment vanishes. In the original spectral variable this
is precisely the constancy of the mean at `(a+b)/2`. -/
theorem continuous_spectrum_centered_moment (c : ℝ) (k : ℕ) :
    (∫ t : ℝ in (-1)..1, t * ((-c * t) ^ k) ^ 2) = 0 := by
  have hpoint : (fun t : ℝ => t * ((-c * t) ^ k) ^ 2) =
      (fun t : ℝ => c ^ (2 * k) * t ^ (2 * k + 1)) := by
    funext t
    rw [← pow_mul, Nat.mul_comm k 2, mul_pow]
    simp only [pow_mul, neg_sq, pow_succ]
    ring
  rw [hpoint, intervalIntegral.integral_const_mul, symmetric_odd_power_integral, mul_zero]

theorem continuous_spectrum_normalized_norm_square (c : ℝ) (k : ℕ) :
    (∫ t : ℝ in (-1)..1, ((-c * t) ^ k) ^ 2) /
      (∫ _t : ℝ in (-1)..1, (1 : ℝ)) =
      c ^ (2 * k) / (2 * (k : ℝ) + 1) := by
  rw [continuous_spectrum_norm_square]
  simp only [intervalIntegral.integral_const, sub_neg_eq_add, one_add_one_eq_two,
    smul_eq_mul, mul_one]
  ring

open Filter
open scoped Topology

/-- The polynomial loss in the exact continuous-spectrum norm formula has
natural-root limit one. -/
theorem continuous_spectrum_denominator_root_limit :
    Tendsto (fun n : ℕ => (Real.sqrt (2*(n:ℝ)+1))^((n:ℝ)⁻¹)) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => 2*(n:ℝ)+1) atTop atTop :=
    tendsto_atTop_mono (fun n => by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      tendsto_natCast_atTop_atTop
  have hlim := (tendsto_rpow_div_mul_add (1:ℝ) 1 (-1) zero_ne_one).comp ht
  have heq (n : ℕ) : (Real.sqrt (2*(n:ℝ)+1))^((n:ℝ)⁻¹) =
      (2*(n:ℝ)+1)^((1:ℝ)/(1*(2*(n:ℝ)+1)+(-1))) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity : 0 ≤ 2*(n:ℝ)+1)]
    congr 1
    rw [show (1:ℝ)*(2*(n:ℝ)+1)+(-1) = 2*(n:ℝ) by ring,
      one_div, one_div, mul_inv_rev]
    ring
  change Tendsto (fun n : ℕ => (2*(n:ℝ)+1)^((1:ℝ)/(1*(2*(n:ℝ)+1)+(-1)))) atTop (𝓝 1) at hlim
  simpa only [← heq] using hlim

/-- The exact finite-step norm ratio of the multiplication example has the
sharp natural-root limit, including the zero-rate scalar convention. -/
theorem continuous_spectrum_norm_root_limit (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (rootTerm (fun n => c^n / Real.sqrt (2*(n:ℝ)+1))) atTop (𝓝 c) := by
  have heq : rootTerm (fun n => c^n / Real.sqrt (2*(n:ℝ)+1)) =ᶠ[atTop]
      (fun n : ℕ => c / (Real.sqrt (2*(n:ℝ)+1))^((n:ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [rootTerm, Real.div_rpow (pow_nonneg hc n) (Real.sqrt_nonneg _),
      Real.pow_rpow_inv_natCast hc (by omega : n ≠ 0)]
  have hlim : Tendsto (fun n : ℕ => c / (Real.sqrt (2*(n:ℝ)+1))^((n:ℝ)⁻¹)) atTop (𝓝 c) := by
    simpa only [div_one] using tendsto_const_nhds.div continuous_spectrum_denominator_root_limit one_ne_zero
  exact Tendsto.congr' heq.symm hlim

theorem continuous_spectrum_norm_rootFactor (c : ℝ) (hc : 0 ≤ c) :
    rootFactor (fun n => c^n / Real.sqrt (2*(n:ℝ)+1)) = c :=
  (continuous_spectrum_norm_root_limit c hc).limsup_eq

end BB
