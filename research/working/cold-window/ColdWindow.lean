import Lean.Data.Rat

open Lean

namespace ColdWindow

def L : Rat := 5000
def c : Rat := 101 / 100
def G : Rat := (L-c)/2
def q : Rat := 201/200
def b2 : Rat := 749851/120000
def coldBB1 : Rat := 4/(3*L+c)
def coldBB2 : Rat := (3*L+c)/(3*L*L+c*c)

theorem tolerance_value : G/2 = 499899/400 := by decide
theorem initial_window : coldBB2/coldBB1 < 4/5 := by decide
theorem old_secant_is_shorter : 1/5000 < coldBB2 ∧ coldBB2 < 1/3751 := by decide
theorem first_ratio_upper : (1012/1000 : Rat)*(1012/1000)/(1+3750*3750*(44/100000000)) < 4/5 := by decide
theorem reference_third_ratio_upper : (1011/1000 : Rat)*(1011/1000)/(1+3750*3750*(27/1000000000)) < 4/5 := by decide
theorem reference_fourth_ratio_lower : (4/5 : Rat) < 1/((1001/1000)*(103/100)) := by decide
theorem alternative_third_ratio_upper : (201/1000 : Rat)*(201/1000)/(1/10) < 4/5 := by decide
theorem alternative_fourth_ratio_upper : (14/1000 : Rat)*(14/1000)/(6/1000) < 4/5 := by decide
theorem terminal_sq_norm_bound : (1/10000000000 : Rat) + 1/400 < 1/4 := by decide
theorem nonterminal_low_bound :
    (1/2 : Rat) < (999/1000)*(17/20)*(9997/10000)*(9997/10000)*(9997/10000) := by decide
theorem wider_radius_before_norm_minimum : (330 : Rat) < G*q/(q*q+b2) := by decide

end ColdWindow

