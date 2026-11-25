import BB.SecantPerturbation

/-! # Frozen secant-interval pair map used by the nonlinear theorem -/

noncomputable section
namespace BB.Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A previous/current gradient pair with a prescribed consecutive-norm bound. -/
def pairCone (M : ℝ) : Set (E × E) := {z | ‖z.2‖ ≤ M * ‖z.1‖}

/-- The complete frozen BB interval, including its harmless total extension at zero. -/
def frozenMap (H : E →L[ℝ] E) (eta : Set.Icc (0 : ℝ) 1) (z : E × E) : E × E :=
  (z.2, z.2 - BB.Secant.blend eta.1 z.1 (H z.1) • H z.2)

theorem zero_mem_pairCone (M : ℝ) : (0 : E × E) ∈ pairCone M := by
  simp [pairCone]

theorem frozenMap_zero (H : E →L[ℝ] E) (eta : Set.Icc (0 : ℝ) 1) :
    frozenMap H eta 0 = 0 := by simp [frozenMap]

end BB.Local
