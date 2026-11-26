import Lean.Elab.Tactic.Omega

namespace CurvatureProjectionBounds

/-- For rational t=a/b, the two marginal widths are 3(1-t) and 4t.
    This is the unconditional lower bound after clearing the denominator. -/
theorem maximum_lower (a b : Nat) (h : a ≤ b) :
    12*b ≤ max (21*(b-a)) (28*a) := by
  by_cases which : 3*b ≤ 7*a
  · have rhs : 12*b ≤ 28*a := by omega
    exact Nat.le_trans rhs (Nat.le_max_right _ _)
  · have lhs : 12*b ≤ 21*(b-a) := by omega
    exact Nat.le_trans lhs (Nat.le_max_left _ _)

theorem maximum_equality (a b : Nat) (h : a ≤ b) :
    max (21*(b-a)) (28*a) = 12*b ↔ 7*a=3*b := by
  constructor
  · intro eq
    have l : 21*(b-a) ≤ 12*b := eq ▸ Nat.le_max_left (21*(b-a)) (28*a)
    have r : 28*a ≤ 12*b := eq ▸ Nat.le_max_right (21*(b-a)) (28*a)
    omega
  · intro eq
    have l : 21*(b-a)=12*b := by omega
    have r : 28*a=12*b := by omega
    simp [l,r]

theorem sum_lower (a b : Nat) (h : a ≤ b) :
    3*b ≤ 3*(b-a)+4*a := by omega

theorem sum_equality (a b : Nat) (h : a ≤ b) :
    3*(b-a)+4*a=3*b ↔ a=0 := by omega

/-- If both sides must retain one unassigned direction, the two spare
    capacities suffice for every prefix shorter than m−2. -/
theorem spare_capacity (m rank used : Nat)
    (hr : 0 < rank) (hn : rank < m)
    (hu : used < m-2) :
    used < (rank-1)+(m-rank-1) := by omega

example : max (21*(7-3)) (28*3) = 12*7 := by decide

end CurvatureProjectionBounds

