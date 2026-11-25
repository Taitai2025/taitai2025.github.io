import BB.Nonlinear
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# The Dini integral comparison

The Dini condition is expressed as Lebesgue interval integrability of
`omega t / t` on `0..s`. For a nonnegative modulus this is the finite improper
Dini integral. The finite comparison, summability, and uniform scalar
critical-rate theorem below are kernel-checked analytic statements.
-/

namespace BB.Dini

open scoped BigOperators
open MeasureTheory Set

private theorem integrable_subinterval {f : ℝ → ℝ} {s a b : ℝ}
    (hf : IntervalIntegrable f volume 0 s)
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ s) :
    IntervalIntegrable f volume a b := by
  apply hf.mono_set
  rw [uIcc_of_le hab, uIcc_of_le (ha.trans (hab.trans hb))]
  exact Icc_subset_Icc ha hb

/-- One geometric interval controls the sample at its smaller endpoint. -/
theorem geometric_interval_bound
    (omega : ℝ → ℝ) (s gamma : ℝ) (hs : 0 < s)
    (hgamma : 0 < gamma) (hgamma_one : gamma < 1)
    (hmono : Monotone omega)
    (hDini : IntervalIntegrable (fun t => omega t / t) volume 0 s) (n : ℕ) :
    omega (s * gamma ^ (n + 1)) * (-Real.log gamma) ≤
      ∫ t in (s * gamma ^ (n + 1))..(s * gamma ^ n), omega t / t := by
  have hpos (j : ℕ) : 0 < s * gamma ^ j := mul_pos hs (pow_pos hgamma j)
  have hle (j : ℕ) : s * gamma ^ j ≤ s := by
    have := mul_le_mul_of_nonneg_left (pow_le_one j hgamma.le hgamma_one.le) hs.le
    simpa using this
  have hadj : s * gamma ^ (n + 1) ≤ s * gamma ^ n := by
    rw [pow_succ]
    nlinarith [hpos n]
  have hinv : IntervalIntegrable (fun t : ℝ => t⁻¹) volume
      (s * gamma ^ (n + 1)) (s * gamma ^ n) := by
    apply intervalIntegral.intervalIntegrable_inv _ continuousOn_id
    intro t ht
    rw [uIcc_of_le hadj] at ht
    exact ne_of_gt ((hpos (n + 1)).trans_le ht.1)
  have hmain := integrable_subinterval hDini (hpos (n + 1)).le hadj (hle n)
  have hcompare :
      (∫ t in (s * gamma ^ (n + 1))..(s * gamma ^ n),
          omega (s * gamma ^ (n + 1)) * t⁻¹) ≤
      ∫ t in (s * gamma ^ (n + 1))..(s * gamma ^ n), omega t / t := by
    apply intervalIntegral.integral_mono_on hadj
      (hinv.const_mul (omega (s * gamma ^ (n + 1)))) hmain
    intro t ht
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right (hmono ht.1)
    exact inv_nonneg.mpr ((hpos (n + 1)).le.trans ht.1)
  calc
    omega (s * gamma ^ (n + 1)) * (-Real.log gamma) =
        omega (s * gamma ^ (n + 1)) *
          Real.log ((s * gamma ^ n) / (s * gamma ^ (n + 1))) := by
      congr 1
      have hratio : (s * gamma ^ n) / (s * gamma ^ (n + 1)) = gamma⁻¹ := by
        rw [pow_succ]
        field_simp
        ring
      rw [hratio, Real.log_inv]
    _ = ∫ t in (s * gamma ^ (n + 1))..(s * gamma ^ n),
          omega (s * gamma ^ (n + 1)) * t⁻¹ := by
      rw [intervalIntegral.integral_const_mul, integral_inv_of_pos (hpos (n + 1)) (hpos n)]
    _ ≤ ∫ t in (s * gamma ^ (n + 1))..(s * gamma ^ n), omega t / t := hcompare

/-- Telescoping the geometric intervals gives a finite tail-sum bound. -/
theorem geometric_tail_integral_bound
    (omega : ℝ → ℝ) (s gamma : ℝ) (hs : 0 < s)
    (hgamma : 0 < gamma) (hgamma_one : gamma < 1)
    (hmono : Monotone omega)
    (hDini : IntervalIntegrable (fun t => omega t / t) volume 0 s) :
    ∀ n : ℕ, (-Real.log gamma) *
      (∑ j in Finset.range n, omega (s * gamma ^ (j + 1))) ≤
      ∫ t in (s * gamma ^ n)..s, omega t / t := by
  have hpos (j : ℕ) : 0 < s * gamma ^ j := mul_pos hs (pow_pos hgamma j)
  have hle (j : ℕ) : s * gamma ^ j ≤ s := by
    have := mul_le_mul_of_nonneg_left (pow_le_one j hgamma.le hgamma_one.le) hs.le
    simpa using this
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hadj : s * gamma ^ (n + 1) ≤ s * gamma ^ n := by
      rw [pow_succ]
      nlinarith [hpos n]
    have hchunk := geometric_interval_bound omega s gamma hs hgamma hgamma_one hmono hDini n
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (integrable_subinterval hDini (hpos (n + 1)).le hadj (hle n))
      (integrable_subinterval hDini (hpos n).le (hle n) le_rfl)
    rw [Finset.sum_range_succ, mul_add]
    nlinarith

/-- Every sampled partial sum is bounded by the Dini integral. -/
theorem geometric_sum_bound
    (omega : ℝ → ℝ) (s gamma : ℝ) (hs : 0 < s)
    (hgamma : 0 < gamma) (hgamma_one : gamma < 1)
    (hmono : Monotone omega) (homega : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hDini : IntervalIntegrable (fun t => omega t / t) volume 0 s) :
    ∀ n : ℕ, (∑ j in Finset.range n, omega (s * gamma ^ j)) ≤
      omega s + (∫ t in (0 : ℝ)..s, omega t / t) / (-Real.log gamma) := by
  have hlog : 0 < -Real.log gamma := neg_pos.mpr (Real.log_neg hgamma hgamma_one)
  have htotal : 0 ≤ ∫ t in (0 : ℝ)..s, omega t / t := by
    apply intervalIntegral.integral_nonneg hs.le
    intro t ht
    exact div_nonneg (homega t ht.1) ht.1
  intro n
  cases n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact add_nonneg (homega s hs.le) (div_nonneg htotal hlog.le)
  | succ n =>
    have hpos : 0 < s * gamma ^ n := mul_pos hs (pow_pos hgamma n)
    have hle : s * gamma ^ n ≤ s := by
      have := mul_le_mul_of_nonneg_left (pow_le_one n hgamma.le hgamma_one.le) hs.le
      simpa using this
    have hsegment_nonneg : 0 ≤ ∫ t in (0 : ℝ)..(s * gamma ^ n), omega t / t := by
      apply intervalIntegral.integral_nonneg hpos.le
      intro t ht
      exact div_nonneg (homega t ht.1) ht.1
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (integrable_subinterval hDini (le_refl 0) hpos.le hle)
      (integrable_subinterval hDini hpos.le hle le_rfl)
    have htail := geometric_tail_integral_bound omega s gamma hs hgamma hgamma_one hmono hDini n
    have htail' : (∑ j in Finset.range n, omega (s * gamma ^ (j + 1))) ≤
        (∫ t in (0 : ℝ)..s, omega t / t) / (-Real.log gamma) := by
      apply (le_div_iff hlog).mpr
      nlinarith
    rw [Finset.sum_range_succ']
    simp only [pow_zero, mul_one]
    linarith

/-- The nonnegative geometric samples form a summable series. -/
theorem geometric_summable
    (omega : ℝ → ℝ) (s gamma : ℝ) (hs : 0 < s)
    (hgamma : 0 < gamma) (hgamma_one : gamma < 1)
    (hmono : Monotone omega) (homega : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hDini : IntervalIntegrable (fun t => omega t / t) volume 0 s) :
    Summable (fun j : ℕ => omega (s * gamma ^ j)) := by
  apply summable_of_sum_range_le
    (fun j => homega _ (mul_nonneg hs.le (pow_nonneg hgamma.le j)))
  exact geometric_sum_bound omega s gamma hs hgamma hgamma_one hmono homega hDini

/-- The infinite sum satisfies the same explicit integral bound. -/
theorem geometric_tsum_bound
    (omega : ℝ → ℝ) (s gamma : ℝ) (hs : 0 < s)
    (hgamma : 0 < gamma) (hgamma_one : gamma < 1)
    (hmono : Monotone omega) (homega : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hDini : IntervalIntegrable (fun t => omega t / t) volume 0 s) :
    (∑' j : ℕ, omega (s * gamma ^ j)) ≤
      omega s + (∫ t in (0 : ℝ)..s, omega t / t) / (-Real.log gamma) := by
  exact tsum_le_of_sum_range_le
    (geometric_summable omega s gamma hs hgamma hgamma_one hmono homega hDini)
    (geometric_sum_bound omega s gamma hs hgamma hgamma_one hmono homega hDini)

/-- The exact scalar nonlinear rate with the explicit Dini prefactor.

All constants and the recurrence are hypotheses. In particular, this theorem
contains no implicit assertion that a nonlinear secant method has been shown
to satisfy the recurrence. -/
theorem uniform_critical_rate_of_dini
    (v : ℕ → ℝ) (omega : ℝ → ℝ) (c D E gamma epsilon : ℝ)
    (hc : 0 < c) (hv : ∀ n, 0 ≤ v n) (hD : 0 ≤ D)
    (hE : 0 < E) (hepsilon : 0 < epsilon)
    (hgamma : 0 < gamma) (hgamma_one : gamma < 1)
    (hmono : Monotone omega) (homega : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hinit : v 0 ≤ epsilon)
    (hsmall : c + D * omega (E * epsilon) ≤ gamma)
    (hrec : ∀ n, v (n + 1) ≤ (c + D * omega (E * v n)) * v n)
    (hDini : IntervalIntegrable (fun t => omega t / t) volume 0 (E * epsilon)) :
    ∀ n, v n ≤ c ^ n * v 0 *
      Real.exp ((D / c) * (omega (E * epsilon) +
        (∫ t in (0 : ℝ)..(E * epsilon), omega t / t) / (-Real.log gamma))) := by
  apply BB.Nonlinear.uniform_critical_rate v omega c D E gamma epsilon _
    hc hv hD hE.le hgamma.le hgamma_one.le hmono hinit hsmall hrec
  intro n
  have hbound := geometric_sum_bound omega (E * epsilon) gamma
    (mul_pos hE hepsilon) hgamma hgamma_one hmono homega hDini n
  convert hbound using 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

end BB.Dini
