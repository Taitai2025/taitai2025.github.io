import Lean.Data.Rat

open Lean

namespace CoordinateQueryChecks

def payoff (oracleCurvature chosenCurvature step : Rat) : Rat :=
  oracleCurvature * (2 * step - chosenCurvature * step * step)

def balanced (k : Rat) : Rat := 8 * (k + 1) / ((k + 3) * (k + 3))

def castCheck (k : Rat) : Bool :=
  let u := (k + 1) / 2
  let step := 2 / (1 + u)
  decide (payoff 1 1 step = balanced k ∧ payoff u u step = balanced k)

theorem balanced_endpoints_2 : castCheck 2 = true := by decide
theorem balanced_endpoints_5 : castCheck 5 = true := by decide
theorem balanced_endpoints_10 : castCheck 10 = true := by decide
theorem balanced_endpoints_100 : castCheck 100 = true := by decide
theorem unbalanced_upper_2 : payoff 1 1 (2 / 3) = 8 / 9 := by decide

/-- Common reply with v=(4/5,3/5), κ=10. The low Hessian is diagonal with
entries 13/4 and 1. The high Hessian has diagonals 43/7 and off-diagonal -27/7. -/
theorem upper_pair_first_response :
    (43 / 7 : Rat) * (4 / 5) - (27 / 7 : Rat) * (3 / 5) =
      (13 / 4 : Rat) * (4 / 5) := by decide

theorem upper_pair_second_response :
    (-27 / 7 : Rat) * (4 / 5) + (43 / 7 : Rat) * (3 / 5) = 3 / 5 := by decide

theorem upper_pair_top_eigenvalue : (43 / 7 : Rat) - (-27 / 7 : Rat) = 10 := by decide
theorem upper_pair_bottom_eigenvalue : (43 / 7 : Rat) + (-27 / 7 : Rat) = 16 / 7 := by decide

theorem axis_k4_a2_crossing_below :
    payoff 1 1 (2 / 7) = payoff 2 4 (2 / 7) ∧
    payoff 1 1 (2 / 7) < (1 / 2 : Rat) := by decide

theorem axis_k4_a9over4_crossing_above :
    payoff 1 1 (5 / 16) = payoff (9 / 4) 4 (5 / 16) ∧
    (4 / 9 : Rat) < payoff 1 1 (5 / 16) := by decide

#print axioms balanced_endpoints_2
#print axioms balanced_endpoints_5
#print axioms balanced_endpoints_10
#print axioms balanced_endpoints_100
#print axioms unbalanced_upper_2
#print axioms upper_pair_first_response
#print axioms upper_pair_second_response
#print axioms upper_pair_top_eigenvalue
#print axioms upper_pair_bottom_eigenvalue
#print axioms axis_k4_a2_crossing_below
#print axioms axis_k4_a9over4_crossing_above

end CoordinateQueryChecks
