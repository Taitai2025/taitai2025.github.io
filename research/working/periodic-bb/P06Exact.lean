import Lean.Data.Rat

/-
P06 / E01 exact finite-response certificates.
Bindings: main.tex (E01) SHA256
ca7c430b3261be1f4fcaad5d8e454676dab3e216ff39296f59495e354d5d85e8.
Main equations (forced), (rho), (exact-cubic-main), and supplement_r01.tex
lines 272--299 give the rational word responses and their coefficients.
This file checks concrete finite rational arithmetic, not asymptotic rates,
measure-theoretic realization, uniqueness, or the uniform 6400 C^4 bound.
Lean.Rat is the rational implementation shipped with Lean, not Mathlib Rat.
All numerators/denominators here are explicit and all denominators positive.
-/
namespace P06Exact
open Lean

def cyc (xs : Array Rat) (i : Nat) : Rat := xs[i % xs.size]!
def coefficient (q : Array Rat) : Rat :=
  q.foldl (fun total x => total + x * x) 0 / mkRat (2 * Int.ofNat q.size) 1

def boundaryCount (sigma : Array Rat) : Nat :=
  (List.range sigma.size).foldl
    (fun total i => if cyc sigma i = 1 ∧ cyc sigma (i + 1) = 0 then total + 1 else total) 0

def word01 : Array Rat := #[0, 1]
def a01 : Array Rat := #[mkRat 3 4, mkRat 1 4]
def q01 : Array Rat := #[mkRat (-1) 4, mkRat 1 4]

theorem response01 : ∀ i : Fin 2,
    cyc a01 (i.val + 1) - cyc a01 i.val + 2 * cyc a01 (i.val + 1)
      = 2 * cyc word01 i.val := by decide

theorem centered01 : ∀ i : Fin 2,
    cyc q01 i.val = cyc word01 i.val - cyc a01 (i.val + 1) := by decide

theorem coefficient01 : coefficient q01 = mkRat 1 32 := by decide

def word000111 : Array Rat := #[0, 0, 0, 1, 1, 1]
def a000111 : Array Rat :=
  #[mkRat (-3) 4, mkRat (-1) 4, mkRat 5 4, mkRat 7 4, mkRat 5 4, mkRat (-1) 4]
def q000111 : Array Rat :=
  #[mkRat 1 4, mkRat 3 4, mkRat 1 4, mkRat (-1) 4, mkRat (-3) 4, mkRat (-1) 4]

theorem response000111 : ∀ i : Fin 6,
    cyc a000111 (i.val + 1) - cyc a000111 i.val + 2 * cyc a000111 (i.val + 5)
      = 2 * cyc word000111 i.val := by decide

theorem centered000111 : ∀ i : Fin 6,
    cyc q000111 i.val = cyc word000111 i.val - cyc a000111 (i.val + 5) := by decide

theorem coefficient000111 : coefficient q000111 = mkRat 11 96 := by decide

def word001011 : Array Rat := #[0, 0, 1, 0, 1, 1]
def a001011 : Array Rat :=
  #[mkRat 1 28, mkRat 11 28, mkRat 9 28, mkRat 43 28, mkRat 25 28, mkRat (-5) 28]
def q001011 : Array Rat :=
  #[mkRat 5 28, mkRat (-1) 28, mkRat 17 28, mkRat (-9) 28, mkRat (-15) 28, mkRat 3 28]

theorem response001011 : ∀ i : Fin 6,
    cyc a001011 (i.val + 1) - cyc a001011 i.val + 2 * cyc a001011 (i.val + 5)
      = 2 * cyc word001011 i.val := by decide

theorem centered001011 : ∀ i : Fin 6,
    cyc q001011 i.val = cyc word001011 i.val - cyc a001011 (i.val + 5) := by decide

theorem coefficient001011 : coefficient q001011 = mkRat 15 224 := by decide

theorem fewerSwitches : boundaryCount word000111 = 1 ∧ boundaryCount word001011 = 2 := by decide

theorem exactDifference : coefficient q000111 - coefficient q001011 = mkRat 1 21 := by decide

theorem strictCoefficientOrdering : coefficient q001011 < coefficient q000111 := by decide

-- Cleared-denominator integer certificates independently expose the exact sums.
theorem cleared000111 :
    (1*1+3*3+1*1+(-1)*(-1)+(-3)*(-3)+(-1)*(-1) : Int) * 96 =
      11 * (2*6*4*4) := by decide

theorem cleared001011 :
    (5*5+(-1)*(-1)+17*17+(-9)*(-9)+(-15)*(-15)+3*3 : Int) * 224 =
      15 * (2*6*28*28) := by decide

theorem clearedDifference : ((11*224-15*96 : Int)*21) = 96*224 := by decide

#print axioms response01
#print axioms centered01
#print axioms coefficient01
#print axioms response000111
#print axioms centered000111
#print axioms coefficient000111
#print axioms response001011
#print axioms centered001011
#print axioms coefficient001011
#print axioms fewerSwitches
#print axioms exactDifference
#print axioms strictCoefficientOrdering
#print axioms cleared000111
#print axioms cleared001011
#print axioms clearedDifference
end P06Exact

