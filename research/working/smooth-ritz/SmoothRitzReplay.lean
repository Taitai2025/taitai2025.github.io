import Lean.Elab.Tactic.Omega

/-!
Abstract replay and finite-line reduction for a delayed gradient history.
States include the stored phase. All agreement and periodicity hypotheses
are explicit. No analytical facts about smoothness or Ritz roots are assumed.
-/

namespace SmoothRitzReplay

def run {State : Type} (advance : State → State) (initial : State) : Nat → State
  | 0 => initial
  | n + 1 => advance (run advance initial n)

theorem same_run {State : Type} (quad nonlinear : State → State)
    (initial : State) (agree : ∀ n, nonlinear (run quad initial n) = quad (run quad initial n)) :
    ∀ n, run nonlinear initial n = run quad initial n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change nonlinear (run nonlinear initial n) = quad (run quad initial n)
      rw [ih, agree n]

theorem observations_replay {Point Data State : Type}
    (point : State → Point) (obsQuad obsNon : Point → Data)
    (update : State → Data → State) (initial : State)
    (observeOnOrbit : ∀ n,
      let quad := fun st => update st (obsQuad (point st))
      obsNon (point (run quad initial n)) = obsQuad (point (run quad initial n))) :
    ∀ n, run (fun st => update st (obsNon (point st))) initial n =
      run (fun st => update st (obsQuad (point st))) initial n := by
  apply same_run
  intro n
  exact congrArg (update (run (fun st => update st (obsQuad (point st))) initial n))
    (observeOnOrbit n)

/-- Isometric sign return on normalized states toggles between two values. -/
theorem involution_two_values {Vector : Type} (flip : Vector → Vector)
    (involutive : ∀ x, flip (flip x) = x) (x : Vector) (n : Nat) :
    run flip x n = x ∨ run flip x n = flip x := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
      change flip (run flip x n) = x ∨ flip (run flip x n) = flip x
      rcases ih with h | h
      · exact Or.inr (congrArg flip h)
      · exact Or.inl ((congrArg flip h).trans (involutive x))

/-- The phase stays fixed during each application of the full period return. -/
theorem normalized_period {Vector : Type} (period : Nat) (flip : Vector → Vector)
    (seq : Nat → Vector) (ret : ∀ k, seq (k + period) = flip (seq k))
    (n r : Nat) : seq (n * period + r) = run flip (seq r) n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
      rw [Nat.succ_mul]
      have move : n * period + period + r = (n * period + r) + period := by omega
      rw [move, ret, ih]
      rfl

theorem at_most_two_normalized_rays_per_phase {Vector : Type}
    (period : Nat) (flip : Vector → Vector) (seq : Nat → Vector)
    (ret : ∀ k, seq (k + period) = flip (seq k))
    (involutive : ∀ x, flip (flip x) = x) (n r : Nat) :
    seq (n * period + r) = seq r ∨ seq (n * period + r) = flip (seq r) := by
  rw [normalized_period period flip seq ret n r]
  exact involution_two_values flip involutive (seq r) n

example (n : Nat) (sixSweeps : n = 6) : n * 2 = 12 := by omega

#print axioms same_run
#print axioms observations_replay
#print axioms involution_two_values
#print axioms normalized_period
#print axioms at_most_two_normalized_rays_per_phase

end SmoothRitzReplay
