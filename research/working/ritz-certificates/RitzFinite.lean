import Lean.Data.Rat
import Lean.Elab.Tactic.Omega

/-!
Exact certificates for two Ritz working papers, using Lean 4.8.0 only.
No Mathlib, external solver, floating-point oracle, or added axiom is used.
The actual worked spectrum in the minimal-support paper is {1,2,4}.

The rational layer uses Lean.Rat, Lean's exact implementation for decision
procedures, not Mathlib's Rat. Universal interpolation/minimax interfaces
are stated after clearing one common positive denominator, hence over Int.

The reuse layer checks finite matrix products and polynomial/inequality
interfaces. It does not prove the real spectral-radius formula, the logarithm
comparison, optimality over all counts, the invariant polygon, or convergence.
-/

namespace RitzMinimalCertificate
open Lean

def r (n : Int) (d : Nat) : Rat := mkRat n d
def lagrange0 (t : Rat) : Rat := (t - 2) * (t - 4) / 3
def lagrange1 (t : Rat) : Rat := (t - 1) * (t - 4) / (-2)
def lagrange2 (t : Rat) : Rat := (t - 1) * (t - 2) / 6
def tau : Rat := r 1 5
def pStar (t : Rat) : Rat := 1 - t + t * t / 5

theorem vandermonde_derivatives :
    ((1 : Int) - 2) * (1 - 4) = 3 ∧
    ((2 : Int) - 1) * (2 - 4) = -2 ∧
    ((4 : Int) - 1) * (4 - 2) = 6 := by decide

theorem lagrange_at_zero :
    lagrange0 0 = r 8 3 ∧ lagrange1 0 = -2 ∧ lagrange2 0 = r 1 3 := by decide

theorem lagrange_cardinality :
    lagrange0 1 = 1 ∧ lagrange0 2 = 0 ∧ lagrange0 4 = 0 ∧
    lagrange1 1 = 0 ∧ lagrange1 2 = 1 ∧ lagrange1 4 = 0 ∧
    lagrange2 1 = 0 ∧ lagrange2 2 = 0 ∧ lagrange2 4 = 1 := by decide

theorem signed_sum_one :
    lagrange0 0 + lagrange1 0 + lagrange2 0 = 1 := by decide

theorem absolute_sum_five :
    lagrange0 0 - lagrange1 0 + lagrange2 0 = 5 := by decide

theorem exact_tau :
    tau * (lagrange0 0 - lagrange1 0 + lagrange2 0) = 1 ∧
    (0 : Rat) < tau ∧ tau < 1 := by decide

theorem attaining_values :
    pStar 0 = 1 ∧ pStar 1 = tau ∧
    pStar 2 = -tau ∧ pStar 4 = tau := by decide

-- Weighted component energies m=(1/3,1/2,1/6), normalized to sum one.
theorem balanced_energies :
    r 1 3 + r 1 2 + r 1 6 = 1 ∧
    r 1 3 * 3 = r 1 2 * 2 ∧ r 1 2 * 2 = r 1 6 * 6 := by decide

theorem orthogonality_degree_zero :
    r 1 3 * pStar 1 + r 1 2 * pStar 2 + r 1 6 * pStar 4 = 0 := by decide

theorem orthogonality_degree_one :
    r 1 3 * pStar 1 * 1 + r 1 2 * pStar 2 * 2 +
    r 1 6 * pStar 4 * 4 = 0 := by decide

theorem nodal_energy_factors :
    pStar 1 * pStar 1 = r 1 25 ∧
    pStar 2 * pStar 2 = r 1 25 ∧
    pStar 4 * pStar 4 = r 1 25 := by decide

def harmonicEnergy : Rat := r 1 3 / 1 + r 1 2 / 2 + r 1 6 / 4
def harmonicAfter : Rat :=
    r 1 3 * pStar 1 * pStar 1 / 1 +
    r 1 2 * pStar 2 * pStar 2 / 2 +
    r 1 6 * pStar 4 * pStar 4 / 4

theorem exact_harmonic_contraction :
    harmonicEnergy = r 5 8 ∧ harmonicAfter = r 1 40 ∧
    harmonicAfter = harmonicEnergy * tau * tau := by decide

-- Numerator of a rational quadratic with common positive denominator den.
def polyN (a b c t : Int) : Int := a + b * t + c * t * t

theorem integer_interpolation (a b c : Int) :
    8 * polyN a b c 1 - 6 * polyN a b c 2 + polyN a b c 4 = 3 * a := by
  unfold polyN
  omega

-- If |P(1)|,|P(2)|,|P(4)| <= bound/den and P(0)=1,
-- this is the cleared-denominator lower bound den <= 5*bound.
theorem nodal_minimax_lower_bound
    (u v w den bound : Int)
    (hden : 0 < den)
    (hinterp : 8*u - 6*v + w = 3*den)
    (hu : -bound ≤ u ∧ u ≤ bound)
    (hv : -bound ≤ v ∧ v ≤ bound)
    (hw : -bound ≤ w ∧ w ≤ bound) :
    0 < bound ∧ den ≤ 5*bound := by omega

theorem rational_quadratic_lower_bound
    (den b c bound : Int) (hden : 0 < den)
    (h1 : -bound ≤ polyN den b c 1 ∧ polyN den b c 1 ≤ bound)
    (h2 : -bound ≤ polyN den b c 2 ∧ polyN den b c 2 ≤ bound)
    (h4 : -bound ≤ polyN den b c 4 ∧ polyN den b c 4 ≤ bound) :
    den ≤ 5*bound := by
  exact (nodal_minimax_lower_bound
    (polyN den b c 1) (polyN den b c 2) (polyN den b c 4)
    den bound hden (integer_interpolation den b c) h1 h2 h4).2

-- Equality forces alternating nodal values, rather than merely their maxima.
theorem equality_requires_alternation
    (u v w bound : Int)
    (hinterp : 8*u - 6*v + w = 15*bound)
    (hu : -bound ≤ u ∧ u ≤ bound)
    (hv : -bound ≤ v ∧ v ≤ bound)
    (hw : -bound ≤ w ∧ w ≤ bound) :
    u = bound ∧ v = -bound ∧ w = bound := by omega

-- The equality case also fixes the rational quadratic's coefficients.
theorem rational_equality_coefficients (bound b c : Int)
    (h1 : -bound ≤ polyN (5*bound) b c 1 ∧ polyN (5*bound) b c 1 ≤ bound)
    (h2 : -bound ≤ polyN (5*bound) b c 2 ∧ polyN (5*bound) b c 2 ≤ bound)
    (h4 : -bound ≤ polyN (5*bound) b c 4 ∧ polyN (5*bound) b c 4 ≤ bound) :
    b = -5*bound ∧ c = bound := by
  have hi := integer_interpolation (5*bound) b c
  have hi' : 8*polyN (5*bound) b c 1 - 6*polyN (5*bound) b c 2 +
      polyN (5*bound) b c 4 = 15*bound := by omega
  have hv := equality_requires_alternation
    (polyN (5*bound) b c 1) (polyN (5*bound) b c 2)
    (polyN (5*bound) b c 4) bound hi' h1 h2 h4
  unfold polyN at hv
  omega

theorem attaining_integer_quadratic :
    polyN 5 (-5) 1 0 = 5 ∧ polyN 5 (-5) 1 1 = 1 ∧
    polyN 5 (-5) 1 2 = -1 ∧ polyN 5 (-5) 1 4 = 1 := by decide

#print axioms vandermonde_derivatives
#print axioms lagrange_at_zero
#print axioms lagrange_cardinality
#print axioms signed_sum_one
#print axioms absolute_sum_five
#print axioms exact_tau
#print axioms attaining_values
#print axioms balanced_energies
#print axioms orthogonality_degree_zero
#print axioms orthogonality_degree_one
#print axioms nodal_energy_factors
#print axioms exact_harmonic_contraction
#print axioms integer_interpolation
#print axioms nodal_minimax_lower_bound
#print axioms rational_quadratic_lower_bound
#print axioms equality_requires_alternation
#print axioms rational_equality_coefficients
#print axioms attaining_integer_quadratic
end RitzMinimalCertificate


namespace RitzReuseCertificate
open Lean

structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq

def mul (A B : Mat2) : Mat2 :=
  ⟨A.a*B.a + A.b*B.c, A.a*B.b + A.b*B.d,
   A.c*B.a + A.d*B.c, A.c*B.b + A.d*B.d⟩

def M (ell : Nat) : Mat2 := ⟨3 - 2*(Int.ofNat ell), -2, 1, 0⟩
def trace (A : Mat2) : Int := A.a + A.d
def det (A : Mat2) : Int := A.a*A.d - A.b*A.c
def charEval (A : Mat2) (z : Int) : Int :=
  (z - A.a)*(z - A.d) - A.b*A.c

-- Products act on column vectors. The first count is the rightmost factor.
def period1213 : Mat2 := mul (M 3) (mul (M 1) (mul (M 2) (M 1)))

theorem generator_matrices :
    M 1 = ⟨1,-2,1,0⟩ ∧ M 2 = ⟨-1,-2,1,0⟩ ∧
    M 3 = ⟨-3,-2,1,0⟩ ∧ M 4 = ⟨-5,-2,1,0⟩ ∧
    M 5 = ⟨-7,-2,1,0⟩ := by decide

theorem generator_determinant (ell : Nat) : det (M ell) = 2 := by
  unfold det M
  simp

theorem prefix12 :
    mul (M 2) (M 1) = ⟨-3,2,1,-2⟩ := by decide

theorem prefix121 :
    mul (M 1) (mul (M 2) (M 1)) = ⟨-5,6,-3,2⟩ := by decide

theorem exact_period_product :
    period1213 = ⟨21,-22,-5,6⟩ := by decide

theorem exact_trace_determinant :
    trace period1213 = 27 ∧ det period1213 = 16 := by decide

theorem period_cost : (1+2+1+3 : Nat) = 7 := by decide

theorem exact_characteristic (z : Int) :
    charEval period1213 z = z*z - 27*z + 16 := by
  rw [exact_period_product]
  unfold charEval
  simp only [Int.sub_mul, Int.mul_sub]
  omega

theorem discriminant :
    (27 : Int)*27 - 4*16 = 665 ∧ (0 : Int) < 665 := by decide

-- Constant-count matrices: their eigenvalues are negative for ell=4,5.
theorem constant_four_characteristic (z : Int) :
    charEval (M 4) z = z*z + 5*z + 2 := by
  have hm : M 4 = ⟨-5,-2,1,0⟩ := by decide
  rw [hm]
  unfold charEval
  simp only [Int.sub_mul, Int.mul_sub]
  omega

theorem constant_five_characteristic (z : Int) :
    charEval (M 5) z = z*z + 7*z + 2 := by
  have hm : M 5 = ⟨-7,-2,1,0⟩ := by decide
  rw [hm]
  unfold charEval
  simp only [Int.sub_mul, Int.mul_sub]
  omega

def q (n : Int) (d : Nat) : Rat := mkRat n d
def positiveRootPolynomial (ell : Nat) (x : Rat) : Rat :=
  x*x - mkRat (2*(Int.ofNat ell)-3) 1 * x + 2
def periodPolynomial (x : Rat) : Rat := x*x - 27*x + 16

-- Sign brackets required by the analytic real-root argument in the paper.
theorem root5_rational_bracket :
    positiveRootPolynomial 5 (q 67 10) < 0 ∧
    (0 : Rat) < positiveRootPolynomial 5 7 := by decide

theorem root4_rational_bracket :
    positiveRootPolynomial 4 (q 114 25) < 0 ∧
    (0 : Rat) < positiveRootPolynomial 4 (q 2281 500) := by decide

theorem period_root_bracket :
    periodPolynomial 26 < 0 ∧ (0 : Rat) < periodPolynomial 27 := by decide

-- All comparisons below use exact natural-number arithmetic after clearing
-- positive denominators; no logarithm or square-root routine is invoked.
theorem count5_beats_count4_power_interface :
    (67 : Nat)^4 * 500^5 > 2281^5 * 10^4 := by decide

theorem count5_beats_count1_power_interface :
    (67 : Nat)^2 > 2^5 * 10^2 := by decide

theorem count5_beats_count2_power_interface :
    (67 : Nat)^4 > 2^5 * 10^4 := by decide

theorem count5_beats_count3_power_interface :
    (67 : Nat)^3 > 2^5 * 10^3 := by decide

theorem mixed_period_beats_count5_power_interface :
    (26 : Nat)^5 > 7^7 := by decide

-- A shorter root bracket at theta=1.59,1.6 for z^14-27 z^7+16.
-- This checks the integer arithmetic, not root isolation or the polygon.
theorem theta_lower_sign :
    (159 : Nat)^14 + 16*100^14 < 27*159^7*100^7 := by decide

theorem theta_upper_sign :
    (8 : Nat)^14 + 16*5^14 > 27*8^7*5^7 := by decide

#print axioms generator_matrices
#print axioms generator_determinant
#print axioms prefix12
#print axioms prefix121
#print axioms exact_period_product
#print axioms exact_trace_determinant
#print axioms period_cost
#print axioms exact_characteristic
#print axioms discriminant
#print axioms constant_four_characteristic
#print axioms constant_five_characteristic
#print axioms root5_rational_bracket
#print axioms root4_rational_bracket
#print axioms period_root_bracket
#print axioms count5_beats_count4_power_interface
#print axioms count5_beats_count1_power_interface
#print axioms count5_beats_count2_power_interface
#print axioms count5_beats_count3_power_interface
#print axioms mixed_period_beats_count5_power_interface
#print axioms theta_lower_sign
#print axioms theta_upper_sign

end RitzReuseCertificate

