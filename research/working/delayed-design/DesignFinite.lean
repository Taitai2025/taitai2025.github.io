import Lean.Data.Rat
import Lean.Elab.Tactic.Omega

/- Finite rational checks for the delayed-design manuscript.
   The epoch recurrences and global convergence remain separate analytic proofs. -/
namespace DelayedDesign
open Lean

def rat (a : Int) (b : Nat) : Rat := mkRat a b
def contrast (x : Rat) : Rat := 4*x*(1-x)
def firstResidual (x : Rat) : Rat := 2*(1-x)
def secondResidual (x : Rat) : Rat := 2*x
def freshPower (x : Rat) : Rat :=
  let p := firstResidual x
  let q := secondResidual x
  (x*p*p)/(x*p*p+(1-x)*q*q)
def halfPower (x : Rat) : Rat :=
  let p := firstResidual x
  let q := secondResidual x
  (x*p)/(x*p+(1-x)*q)
def affineUpdate (x : Rat) (step : Rat) : Rat :=
  x+step*(freshPower x-x)

theorem balanced_value : contrast (rat 1 2) = 1 := by decide

theorem repeated_initial_rows :
    contrast (rat 1 3) = rat 8 9 ∧ freshPower (rat 1 3) = rat 2 3 := by decide

theorem immediate_fresh_half_updates :
    halfPower (rat 1 3) = rat 1 2 ∧ affineUpdate (rat 1 3) (rat 1 2) = rat 1 2 := by decide

theorem first_uncapped_cost_step :
    affineUpdate (rat 1 3) (rat 1 4) = rat 5 12 ∧
    1-contrast (rat 5 12) = (1-contrast (rat 1 3))/4 := by decide

def trapScale : Rat := rat 101 100
def pairValue (x y : Rat) : Rat :=
  trapScale*(101*101)*x*y/(100*100*x+y)

theorem informative_pair_optimal_value :
    rat 1 101 + rat 100 101 = 1 ∧
    pairValue (rat 1 101) (rat 100 101) = trapScale := by decide

theorem limiting_efficiency_ratio : 1/trapScale = rat 100 101 := by decide

theorem projected_growth_margin : rat 21 20 < rat 357679 337174 := by decide

theorem covariance_growth_margin :
    rat 10019 10000 < rat 165324684 164997379 := by decide

theorem finite_start_margin :
    (rat 10019 10000-rat 1001 1000)*5000000-3000 = 1500 := by decide

theorem certified_interval_example :
    rat 1481081 6516050 < rat 6931 29773 ∧
    rat 743 3344 < rat 4553852 18369941 := by decide

#print axioms balanced_value
#print axioms repeated_initial_rows
#print axioms immediate_fresh_half_updates
#print axioms first_uncapped_cost_step
#print axioms informative_pair_optimal_value
#print axioms limiting_efficiency_ratio
#print axioms projected_growth_margin
#print axioms covariance_growth_margin
#print axioms finite_start_margin
#print axioms certified_interval_example
end DelayedDesign
