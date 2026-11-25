import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Scalar perturbation part of the nonlinear BB theorem

These theorems verify the scalar argument after a common Lyapunov function and
its nonlinear perturbation estimate have been established. They do not assert
that the Hessian, secant, or cone hypotheses of a Euclidean optimization problem
have already been proved. The geometric-series majorant in the last theorem is
an explicit hypothesis; a Dini integral comparison is a separate obligation.
-/

namespace BB.Nonlinear

open scoped BigOperators

/-- A uniformly small relative perturbation yields a geometric bootstrap. -/
theorem geometric_bootstrap
    (v : ℕ → ℝ) (omega : ℝ → ℝ) (c D E gamma epsilon : ℝ)
    (hv : ∀ n, 0 ≤ v n) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgamma : 0 ≤ gamma) (hgamma_one : gamma ≤ 1)
    (hmono : Monotone omega) (hinit : v 0 ≤ epsilon)
    (hsmall : c + D * omega (E * epsilon) ≤ gamma)
    (hrec : ∀ n, v (n + 1) ≤ (c + D * omega (E * v n)) * v n) :
    ∀ n, v n ≤ gamma ^ n * v 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hpow : gamma ^ n ≤ 1 := pow_le_one n hgamma hgamma_one
    have hveps : v n ≤ epsilon :=
      (ih.trans (by nlinarith [hv 0])).trans hinit
    have hcoef : c + D * omega (E * v n) ≤ gamma :=
      (add_le_add_left
        (mul_le_mul_of_nonneg_left
          (hmono (mul_le_mul_of_nonneg_left hveps hE)) hD) c).trans hsmall
    calc
      v (n + 1) ≤ (c + D * omega (E * v n)) * v n := hrec n
      _ ≤ gamma * v n := mul_le_mul_of_nonneg_right hcoef (hv n)
      _ ≤ gamma * (gamma ^ n * v 0) := mul_le_mul_of_nonneg_left ih hgamma
      _ = gamma ^ (n + 1) * v 0 := by rw [pow_succ]; ring

/-- Exponentiating the finite accumulated relative error bounds a perturbed
geometric recurrence. No infinite sum is used in this lemma. -/
theorem finite_perturbation_bound
    (v b : ℕ → ℝ) (c D : ℝ) (hc : 0 < c)
    (hv : ∀ n, 0 ≤ v n)
    (hrec : ∀ n, v (n + 1) ≤ (c + D * b n) * v n) :
    ∀ n, v n ≤ c ^ n * v 0 * Real.exp ((D / c) * ∑ j in Finset.range n, b j) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hfac : c + D * b n ≤ c * Real.exp ((D / c) * b n) := by
      calc
        c + D * b n = c * (1 + (D / c) * b n) := by field_simp
        _ ≤ c * Real.exp ((D / c) * b n) :=
          mul_le_mul_of_nonneg_left
            (by simpa [add_comm] using Real.add_one_le_exp ((D / c) * b n)) hc.le
    calc
      v (n + 1) ≤ (c + D * b n) * v n := hrec n
      _ ≤ (c * Real.exp ((D / c) * b n)) * v n :=
        mul_le_mul_of_nonneg_right hfac (hv n)
      _ ≤ (c * Real.exp ((D / c) * b n)) *
            (c ^ n * v 0 * Real.exp ((D / c) * ∑ j in Finset.range n, b j)) :=
        mul_le_mul_of_nonneg_left ih (mul_nonneg hc.le (Real.exp_pos _).le)
      _ = c ^ (n + 1) * v 0 *
            Real.exp ((D / c) * ∑ j in Finset.range (n + 1), b j) := by
        rw [Finset.sum_range_succ, mul_add, Real.exp_add, pow_succ]
        ring

/-- A uniform upper bound on every partial sum gives the critical exponential
factor, with one explicit prefactor. -/
theorem critical_bound_of_partial_sum_bound
    (v b : ℕ → ℝ) (c D A : ℝ) (hc : 0 < c) (hD : 0 ≤ D)
    (hv : ∀ n, 0 ≤ v n)
    (hrec : ∀ n, v (n + 1) ≤ (c + D * b n) * v n)
    (hsum : ∀ n, (∑ j in Finset.range n, b j) ≤ A) :
    ∀ n, v n ≤ c ^ n * v 0 * Real.exp ((D / c) * A) := by
  intro n
  refine (finite_perturbation_bound v b c D hc hv hrec n).trans ?_
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hsum n) (div_nonneg hD hc.le)))
    (mul_nonneg (pow_nonneg hc.le n) (hv 0))

/-- The bootstrap and accumulated-error argument, uniform for all v(0)≤epsilon.
The majorant is sampled at epsilon, not at the individual initial value. -/
theorem uniform_critical_rate
    (v : ℕ → ℝ) (omega : ℝ → ℝ) (c D E gamma epsilon A : ℝ)
    (hc : 0 < c) (hv : ∀ n, 0 ≤ v n) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgamma : 0 ≤ gamma) (hgamma_one : gamma ≤ 1)
    (hmono : Monotone omega) (hinit : v 0 ≤ epsilon)
    (hsmall : c + D * omega (E * epsilon) ≤ gamma)
    (hrec : ∀ n, v (n + 1) ≤ (c + D * omega (E * v n)) * v n)
    (hsum : ∀ n, (∑ j in Finset.range n, omega (E * (gamma ^ j * epsilon))) ≤ A) :
    ∀ n, v n ≤ c ^ n * v 0 * Real.exp ((D / c) * A) := by
  have hboot := geometric_bootstrap v omega c D E gamma epsilon hv hD hE
    hgamma hgamma_one hmono hinit hsmall hrec
  apply critical_bound_of_partial_sum_bound v
    (fun j => omega (E * (gamma ^ j * epsilon))) c D A hc hD hv _ hsum
  intro n
  have harg : E * v n ≤ E * (gamma ^ n * epsilon) :=
    mul_le_mul_of_nonneg_left
      ((hboot n).trans (mul_le_mul_of_nonneg_left hinit (pow_nonneg hgamma n))) hE
  exact (hrec n).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add_left (mul_le_mul_of_nonneg_left (hmono harg) hD) c) (hv n))

/-- A summable nonnegative sampled modulus supplies the majorant used above. -/
theorem uniform_critical_rate_of_summable
    (v : ℕ → ℝ) (omega : ℝ → ℝ) (c D E gamma epsilon : ℝ)
    (hc : 0 < c) (hv : ∀ n, 0 ≤ v n) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hgamma : 0 ≤ gamma) (hgamma_one : gamma ≤ 1)
    (hmono : Monotone omega) (homega : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hinit : v 0 ≤ epsilon)
    (hsmall : c + D * omega (E * epsilon) ≤ gamma)
    (hrec : ∀ n, v (n + 1) ≤ (c + D * omega (E * v n)) * v n)
    (hsummable : Summable (fun j : ℕ => omega (E * (gamma ^ j * epsilon)))) :
    ∀ n, v n ≤ c ^ n * v 0 *
      Real.exp ((D / c) * ∑' j : ℕ, omega (E * (gamma ^ j * epsilon))) := by
  apply uniform_critical_rate v omega c D E gamma epsilon
    (∑' j : ℕ, omega (E * (gamma ^ j * epsilon))) hc hv hD hE
    hgamma hgamma_one hmono hinit hsmall hrec
  intro n
  apply sum_le_tsum (Finset.range n) _ hsummable
  intro j _
  exact homega _ (mul_nonneg hE (mul_nonneg (pow_nonneg hgamma j) ((hv 0).trans hinit)))

end BB.Nonlinear
