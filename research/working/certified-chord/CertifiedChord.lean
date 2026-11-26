import Lean.Data.Rat

open Lean

namespace CertifiedChord

def f (x : Rat) : Rat :=
  if x ≤ 0 then x * x / 2
  else if x ≤ 1 / 2 then x * x / 2 - x * x * x / 6
  else 5 / 48 + (3 / 8) * (x - 1 / 2) + (x - 1 / 2) * (x - 1 / 2) / 4

def g (x : Rat) : Rat :=
  if x ≤ 0 then x else if x ≤ 1 / 2 then x - x * x / 2 else 3 / 8 + (x - 1 / 2) / 2

def x0 : Rat := 1 / 4096
def theta : Rat := g x0 / 1048576
def x1 : Rat := x0 - g x0 / 4
def a : Rat := (x0 - x1) / (g x0 - g x1)
def p : Rat := x1 - a * g x1
def t : Rat := g x1 / (g x1 - g p)
def U : Rat := t * (1 - t) * a * a * g x1 * g x1 / 2
def q : Rat := x1 - t * a * g x1
def b : Rat := (x1 - p) / (g x1 - g p)
def r : Rat := p - b * g p

theorem x1_value : x1 = 24577 / 134217728 := by decide
theorem theta_value : theta = 8191 / 35184372088832 := by decide
theorem a_unclipped : (1 / 4 : Rat) < a ∧ a < 2 := by decide
theorem b_unclipped : (1 / 4 : Rat) < b ∧ b < 2 := by decide
theorem trial_signs : (0 : Rat) < x1 ∧ x1 < 1 / 2 ∧ p < 0 := by decide
theorem terminal_param : (0 : Rat) < t ∧ t < 1 := by decide
theorem chord_zero : g x1 + t * (g p - g x1) = 0 := by decide
theorem q_value : q = 604028929 / 295093865557572718592 := by decide
theorem same_terminal : q = r := by decide
theorem first_nonterminal : (100000 : Rat) * theta < g x1 := by decide
theorem second_nonterminal : (96 : Rat) * theta < -g p ∧ -g p < 97 * theta := by decide
theorem strict_upper_certificate : 0 < U ∧ U < (9 / 1000 : Rat) * theta := by decide
theorem true_terminal : 0 < g q ∧ g q < (9 / 1000 : Rat) * theta := by decide
theorem cold_pass :
    (9 / 1000000000 : Rat) < f x0 - g x0 * g x0 / 16 - f x1 := by decide
theorem second_pass :
    (2 / 100000000 : Rat) < f x0 - a * g x1 * g x1 / 4 - f p := by decide
theorem third_pass :
    (2 / 100000000 : Rat) < f x0 - b * p * p / 4 - f r := by decide

example : (1 + 2 + 0 + 1 : Nat) = 1 + 3 + 0 := by decide
example : (1 + 2 + 1 : Nat) = 1 + 3 := by decide

#print axioms same_terminal
#print axioms second_nonterminal
#print axioms strict_upper_certificate
#print axioms true_terminal
#print axioms cold_pass
#print axioms second_pass
#print axioms third_pass

end CertifiedChord
