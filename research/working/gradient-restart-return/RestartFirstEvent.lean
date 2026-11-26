import Lean.Data.Rat

open Lean

namespace RestartFirstEvent

/-- The residual pair at trials k and k+1. -/
def residualPair (s : Rat) : Nat → Rat × Rat
  | 0 => (1, s)
  | k + 1 =>
    let pair := residualPair s k
    let momentum : Rat := mkRat (Int.ofNat k) (k+3)
    (pair.2, s * (pair.2 + momentum * (pair.2 - pair.1)))

def residual (s : Rat) (k : Nat) : Rat := (residualPair s k).1

theorem pair_successor (s : Rat) (k : Nat) :
    residualPair s (k+1) =
      ((residualPair s k).2,
        s * ((residualPair s k).2 + mkRat (Int.ofNat k) (k+3) *
          ((residualPair s k).2 - (residualPair s k).1))) := rfl

theorem first_in_pair (s : Rat) (k : Nat) :
    (residualPair s k).2 = residual s (k+1) := rfl

def criterion (s : Rat) (k : Nat) : Rat :=
  let pair := residualPair s (k-1)
  (1-s)/s * pair.2 * (pair.2-pair.1)

def testTwoModes (s f a b : Rat) (k : Nat) : Bool :=
  let trialIsZero := (a == 0 || residual s k == 0) && (b == 0 || residual f k == 0)
  trialIsZero || decide (0 < a * criterion s k + b * criterion f k)

def testOneMode (s : Rat) (k : Nat) : Bool :=
  (residual s k == 0) || decide (0 < criterion s k)

def firstEventUpTo (trigger : Nat → Bool) (budget : Nat) : Option Nat :=
  (List.range budget).map (fun j => j+1) |>.find? trigger

def slow1 : Rat := 7599/10000
def slow2 : Rat := 49450896852043/50000000000000
def fast : Rat := 1/2
def tieWeight : Rat := criterion slow1 7 / (-criterion fast 7)

set_option maxRecDepth 12000
set_option maxHeartbeats 2000000
theorem scalar_trial_seven : firstEventUpTo (testOneMode slow1) 8 = some 7 := by decide
theorem mixed_trial_eight : firstEventUpTo (testTwoModes slow1 fast 1 1) 8 = some 8 := by decide
theorem all_weight_certificate_eight :
    0 < criterion slow1 5 + 32 * criterion slow1 8 ∧
    0 < criterion fast 5 + 32 * criterion fast 8 := by decide
theorem zero_criterion_is_accepted :
    0 < tieWeight ∧ criterion slow1 7 + tieWeight * criterion fast 7 = 0 ∧
    testTwoModes slow1 fast 1 tieWeight 7 = false := by decide
theorem first_event_after_tie : firstEventUpTo (testTwoModes slow1 fast 1 tieWeight) 8 = some 8 := by decide
theorem zero_iterate_terminal :
    residual (1/5 : Rat) 3 = 0 ∧ firstEventUpTo (testOneMode (1/5)) 3 = some 3 := by decide

theorem scalar_trial_thirtysix : firstEventUpTo (testOneMode slow2) 37 = some 36 := by decide
theorem mixed_trial_thirtyseven : firstEventUpTo (testTwoModes slow2 fast 4 1) 37 = some 37 := by decide
theorem all_weight_certificate_thirtyseven :
    0 < criterion slow2 5 + 64 * criterion slow2 37 ∧
    0 < criterion fast 5 + 64 * criterion fast 37 := by decide

end RestartFirstEvent

