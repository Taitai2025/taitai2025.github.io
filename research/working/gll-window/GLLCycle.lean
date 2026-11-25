import Lean.Data.Rat
import Lean.Elab.Tactic.Omega

/-!
A core-Lean certificate for the exact scalar GLL example.
No Mathlib, external solver, evaluation oracle, or added axiom is used.

Lean.Rat is the exact normalized rational implementation supplied with Lean.
It is not Mathlib's Rat. Every closed rational claim below is a kernel-checked
decidable proposition. The inductive statements quantify over every natural M.

What is modeled: one normalized cycle starting at x = 1, sigma = 1/4,
eta = 2/5, initial step 1/2, M accepted steps of size 2, and a final trial
of size 2 shortened once to 4/5. The numerical and indexing parts are proved
separately. This is not a formalization of the full real-valued GLL algorithm.
-/

namespace GLLCycle

open Lean

def sigma : Rat := mkRat 1 4
def eta : Rat := mkRat 2 5
def half : Rat := mkRat 1 2
def shortened : Rat := mkRat 4 5
def tenth : Rat := mkRat 1 10
def f (x : Rat) : Rat := x * x / 2
def step (alpha x : Rat) : Rat := (1 - alpha) * x
def accepts (alpha x reference : Rat) : Prop :=
  f (step alpha x) ≤ reference - sigma * alpha * x * x

instance (alpha x reference : Rat) : Decidable (accepts alpha x reference) :=
  inferInstanceAs (Decidable (_ ≤ _))

theorem acceptance_threshold :
    (2 : Rat) * (1 - sigma) = mkRat 3 2 := by decide

theorem contraction_steps_below_threshold :
    half ≤ (2 : Rat) * (1 - sigma) ∧
    shortened ≤ (2 : Rat) * (1 - sigma) := by decide

theorem half_step_and_energy :
    step half 1 = half ∧ f half = mkRat 1 8 := by decide

theorem half_step_accepted : accepts half 1 (f 1) := by decide

-- For alpha = 2 and sigma = 1/4, F = 2 f(x) is the equality threshold.
theorem doubled_reference_equality :
    f (step 2 1) = (2 : Rat) * f 1 - sigma * 2 * (1 : Rat) * 1 := by decide

theorem equal_reference_rejects : ¬ accepts 2 1 (f 1) := by decide
theorem doubled_reference_accepts : accepts 2 1 ((2 : Rat) * f 1) := by decide
theorem quadrupled_reference_accepts : accepts 2 1 ((4 : Rat) * f 1) := by decide

theorem one_shortening : eta * 2 = shortened := by decide
theorem shortened_step_value : step shortened 1 = mkRat 1 5 := by decide
theorem shortened_step_accepted : accepts shortened 1 (f 1) := by decide

-- These two identities allow an induction over an arbitrary memory length.
theorem flip_positive : step 2 half = -half := by decide
theorem flip_negative : step 2 (-half) = half := by decide

def flips : Nat → Rat
  | 0 => half
  | n + 1 => step 2 (flips n)

theorem all_flip_states (n : Nat) :
    flips n = half ∨ flips n = -half := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      cases ih with
      | inl h =>
          right
          simp only [flips, h]
          exact flip_positive
      | inr h =>
          left
          simp only [flips, h]
          exact flip_negative

theorem all_flip_energies (n : Nat) :
    f (flips n) = mkRat 1 8 := by
  cases all_flip_states n with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

-- The cycle's starting objective is four times every intermediate objective.
theorem starting_reference_accepts_every_flip (n : Nat) :
    accepts 2 (flips n) (f 1) := by
  cases all_flip_states n with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

-- Once the starting point has left the window, all retained energies coincide.
theorem last_trial_rejected (M : Nat) :
    ¬ accepts 2 (flips M) (f (flips M)) := by
  cases all_flip_states M with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

theorem first_backtrack_accepted (M : Nat) :
    accepts shortened (flips M) (f (flips M)) := by
  cases all_flip_states M with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

def cycleEnd (M : Nat) : Rat := step shortened (flips M)

theorem cycle_end_states (M : Nat) :
    cycleEnd M = tenth ∨ cycleEnd M = -tenth := by
  cases all_flip_states M with
  | inl h =>
      left
      unfold cycleEnd
      rw [h]
      decide
  | inr h =>
      right
      unfold cycleEnd
      rw [h]
      decide

theorem cycle_energy_factor (M : Nat) :
    f (cycleEnd M) = f 1 / 100 := by
  cases cycle_end_states M with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

theorem cycle_end_nonzero (M : Nat) : cycleEnd M ≠ 0 := by
  cases cycle_end_states M with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

/- A window includes all indices i from max(0,k-M) through k.
Nat subtraction already truncates at zero. -/
def inWindow (M k i : Nat) : Prop := k - M ≤ i ∧ i ≤ k

-- For the first M trials of size 2, the cycle start j is still retained.
theorem cycle_start_in_early_window
    (j M r : Nat) (hr : 1 ≤ r) (hM : r ≤ M) :
    inWindow M (j + r) j := by
  unfold inWindow
  omega

-- At the final trial k=j+M+1 the retained indices are exactly j+1,...,j+M+1.
theorem last_window_exact (j M i : Nat) :
    inWindow M (j + M + 1) i ↔
      j + 1 ≤ i ∧ i ≤ j + M + 1 := by
  unfold inWindow
  omega

theorem cycle_start_not_in_last_window (j M : Nat) :
    ¬ inWindow M (j + M + 1) j := by
  unfold inWindow
  omega

theorem cycle_last_trial_partition (M r : Nat)
    (hM : r ≤ M + 1) :
    r ≤ M ∨ r = M + 1 := by omega

-- A single statement packages the normalized final rejection, first acceptance,
-- energy contraction, and nontermination facts for every memory length.
theorem normalized_cycle_certificate (M : Nat) :
    (¬ accepts 2 (flips M) (f (flips M))) ∧
    accepts (eta * 2) (flips M) (f (flips M)) ∧
    f (cycleEnd M) = f 1 / 100 ∧ cycleEnd M ≠ 0 := by
  rw [one_shortening]
  exact ⟨last_trial_rejected M, first_backtrack_accepted M,
         cycle_energy_factor M, cycle_end_nonzero M⟩

-- The empty early phase (M=0) is included in all theorems above.
theorem zero_memory_cycle : cycleEnd 0 = tenth := by decide

#print axioms acceptance_threshold
#print axioms contraction_steps_below_threshold
#print axioms half_step_and_energy
#print axioms half_step_accepted
#print axioms doubled_reference_equality
#print axioms equal_reference_rejects
#print axioms doubled_reference_accepts
#print axioms quadrupled_reference_accepts
#print axioms one_shortening
#print axioms shortened_step_value
#print axioms shortened_step_accepted
#print axioms flip_positive
#print axioms flip_negative
#print axioms all_flip_states
#print axioms all_flip_energies
#print axioms starting_reference_accepts_every_flip
#print axioms last_trial_rejected
#print axioms first_backtrack_accepted
#print axioms cycle_end_states
#print axioms cycle_energy_factor
#print axioms cycle_end_nonzero
#print axioms cycle_start_in_early_window
#print axioms last_window_exact
#print axioms cycle_start_not_in_last_window
#print axioms cycle_last_trial_partition
#print axioms zero_memory_cycle
#print axioms normalized_cycle_certificate

end GLLCycle

