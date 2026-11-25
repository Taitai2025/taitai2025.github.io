import Lean.Data.Rat
import Lean.Elab.Tactic.Omega

/- Exact rational certificates for the two cold-start comparisons.
   The analytic proof of the moving-window estimate and the real-variable
   hypotheses is in the paper. The checks below cover both two-step traces. -/
namespace TrialValue
open Lean

def R (n : Int) (d : Nat) : Rat := mkRat n d

def mu : Rat := R 1 2
def L : Rat := 4
def epsilon : Rat := R 1 1048576
def cold : Rat := R 1 4
def sigma : Rat := R 1 4
def uno : Rat := 1

def absR (x : Rat) : Rat := if x < 0 then -x else x

def trial (x g a : Rat) : Rat := x - a * g
def armijo (reference g a : Rat) : Rat := reference - sigma * a * g * g
def bb1 (s y : Rat) : Rat := s * s / (s * y)
def bb2 (s y : Rat) : Rat := s * y / (y * y)
def modelCurvature (fx fp a g : Rat) : Rat :=
  2 * (fp - fx + a * g * g) / (a * a * g * g)

def quartic (x : Rat) : Rat := x*x - x*x*x*x/12
def quarticG (x : Rat) : Rat := 2*x - x*x*x/3
def quarticH (x : Rat) : Rat := 2-x*x
def u : Rat := R 1 256
def rQ : Rat := trial u (quarticG u) cold
def sQ : Rat := rQ - u
def yQ : Rat := quarticG rQ - quarticG u
def aQ : Rat := bb1 sQ yQ
def pQ : Rat := trial rQ (quarticG rQ) aQ
def betaQ : Rat := modelCurvature (quartic rQ) (quartic pQ) aQ (quarticG rQ)
def bQ : Rat := 1 / betaQ
def qQ : Rat := trial rQ (quarticG rQ) bQ
def thetaQ : Rat := epsilon * quarticG u

theorem quartic_joins :
    quartic (R 1 2) = R 47 192 ∧ quartic (R (-1) 2) = R 47 192 ∧
    quarticG (R 1 2) = R 23 24 ∧ quarticG (R (-1) 2) = R (-23) 24 ∧
    quarticH (R 1 2) = R 7 4 ∧ quarticH (R (-1) 2) = R 7 4 := by decide

theorem quartic_points_in_inner_interval :
    (0 : Rat) < rQ ∧ rQ < u ∧ u < R 1 2 ∧ R (-1) 2 < pQ ∧
    pQ < qQ ∧ qQ < (0 : Rat) := by decide

theorem quartic_cold_trial :
    thetaQ < quarticG u ∧ thetaQ < quarticG rQ ∧
    quartic rQ < armijo (quartic u) (quarticG u) cold := by decide

theorem quartic_secants :
    (0 : Rat) < sQ * yQ ∧ (0 : Rat) < yQ*yQ ∧
    bb2 sQ yQ = aQ ∧ R 4 5 < bb2 sQ yQ / aQ ∧
    R 1 4 < aQ ∧ aQ < 2 := by decide

theorem quartic_parent_trial :
    quartic rQ < quartic u ∧
    quartic pQ < armijo (quartic u) (quarticG rQ) aQ := by decide

theorem quartic_reselected_trial :
    aQ * betaQ > uno ∧ (0 : Rat) < bQ ∧ bQ < aQ ∧
    quartic qQ < armijo (quartic u) (quarticG rQ) bQ := by decide

theorem quartic_crosses_only_at_new_point :
    quarticG qQ < (0 : Rat) ∧ absR (quarticG qQ) < thetaQ ∧
    thetaQ < absR (quarticG pQ) := by decide

-- For the continuum argument, this section computes the r = 1 member.
def tentG (x : Rat) : Rat :=
    if x ≤ 0 then R 3 2 * x
    else if x ≤ 1 then R 3 2*x+x*x/2
    else if x ≤ 2 then 2+R 5 2*(x-1)-(x-1)*(x-1)/2
    else 4+R 3 2*(x-2)

def tent (x : Rat) : Rat :=
    if x ≤ 0 then R 3 4*x*x
    else if x ≤ 1 then R 3 4*x*x+x*x*x/6
    else if x ≤ 2 then R 11 12+2*(x-1)+R 5 4*(x-1)*(x-1)-(x-1)*(x-1)*(x-1)/6
    else 4+4*(x-2)+R 3 4*(x-2)*(x-2)

def rT : Rat := trial 2 (tentG 2) cold
def sT : Rat := rT - 2
def yT : Rat := tentG rT - tentG 2
def aT : Rat := bb1 sT yT
def pT : Rat := trial rT (tentG rT) aT
def betaT : Rat := modelCurvature (tent rT) (tent pT) aT (tentG rT)
def bT : Rat := 1 / betaT
def qT : Rat := trial rT (tentG rT) bT
def thetaT : Rat := epsilon * tentG 2

theorem tent_initial_values :
    tent 2 = 4 ∧ tentG 2 = 4 ∧ rT = 1 ∧ tent rT = R 11 12∧ tentG rT = 2 := by decide

theorem tent_cold_trial :
    thetaT < tentG 2 ∧ thetaT < tentG rT ∧
    tent rT < armijo (tent 2) (tentG 2) cold := by decide

theorem tent_secants :
    (0 : Rat) < sT * yT ∧ (0 : Rat) < yT*yT ∧
    aT = R 1 2 ∧ bb2 sT yT = aT ∧ R 4 5 < bb2 sT yT / aT := by decide

theorem tent_parent_trial :
    tent rT < tent 2 ∧ pT = (0 : Rat) ∧
    tent pT < armijo (tent 2) (tentG rT) aT := by decide

theorem tent_reselected_trial :
    aT*betaT > uno ∧ betaT = R 13 6 ∧ (0 : Rat) < bT ∧ bT < aT ∧
    qT = R 1 13 ∧ tent qT < armijo (tent 2) (tentG rT) bT := by decide

theorem tent_crosses_only_at_original_point :
    absR (tentG pT) ≤ thetaT ∧
    absR (tentG qT) = R 20 169 ∧ thetaT < absR (tentG qT) := by decide

-- After clearing a common positive denominator the two scalar bounds
-- combine to exactly the moving-window coefficient used in the paper.
theorem eliminate_window (h D z : Int)
    (armijoBound : 64*h ≤ 64*D - 3*z) (smoothBound : h ≤ 7*z) :
    451*h ≤ 448*D := by omega

theorem slow_reselection_query_bounds (n j m : Nat) (steps : 3 ≤ n) (extra : 1 ≤ m) :
    5 ≤ 1 + n + j + m ∧ 4 ≤ 1 + n := by omega

theorem slow_reference_query_bounds (n j : Nat) (steps : 3 ≤ n) :
    4 ≤ 1 + n + j ∧ 4 ≤ 1 + n := by omega

theorem counting_includes_the_extra_value (j n m : Nat) :
    (1+n+j+m)-(1+n)=j+m := by omega

#print axioms quartic_joins
#print axioms quartic_points_in_inner_interval
#print axioms quartic_cold_trial
#print axioms quartic_secants
#print axioms quartic_parent_trial
#print axioms quartic_reselected_trial
#print axioms quartic_crosses_only_at_new_point
#print axioms tent_initial_values
#print axioms tent_cold_trial
#print axioms tent_secants
#print axioms tent_parent_trial
#print axioms tent_reselected_trial
#print axioms tent_crosses_only_at_original_point
#print axioms eliminate_window
#print axioms slow_reselection_query_bounds
#print axioms slow_reference_query_bounds
#print axioms counting_includes_the_extra_value
end TrialValue
