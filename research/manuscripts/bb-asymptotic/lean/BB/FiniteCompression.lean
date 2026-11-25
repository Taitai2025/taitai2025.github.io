import BB.LinearCoordinates
import Mathlib.Analysis.InnerProductSpace.Projection

/-!
# Exact finite-dimensional compression of a prescribed BB segment

The space contains the finitely many gradients and their operator images.
Orthogonal compression preserves symmetry and the quadratic-form bounds and
reproduces each gradient through the prescribed horizon.  Consequently a
dimension-independent finite-dimensional estimate transfers to a real Hilbert
space without presupposing a projection-valued spectral theorem.
-/

namespace BB
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def linearBBOrbit (H : E →ₗ[ℝ] E) (g₀ g₁ : E) : ℕ → E
  | 0 => g₀
  | 1 => g₁
  | n+2 => operatorGradientStep H (operatorBB1 H (linearBBOrbit H g₀ g₁ n))
      (linearBBOrbit H g₀ g₁ (n+1))

@[simp] theorem linear_bb_orbit_zero (H : E →ₗ[ℝ] E) (g₀ g₁ : E) :
    linearBBOrbit H g₀ g₁ 0 = g₀ := rfl

@[simp] theorem linear_bb_orbit_one (H : E →ₗ[ℝ] E) (g₀ g₁ : E) :
    linearBBOrbit H g₀ g₁ 1 = g₁ := rfl

theorem linear_bb_orbit_update (H : E →ₗ[ℝ] E) (g₀ g₁ : E) (n : ℕ) :
    linearBBOrbit H g₀ g₁ (n+2) =
      operatorGradientStep H (operatorBB1 H (linearBBOrbit H g₀ g₁ n))
        (linearBBOrbit H g₀ g₁ (n+1)) := rfl

def operatorCompression (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] : V →L[ℝ] V :=
  ((orthogonalProjection V).comp A).comp V.subtypeL

theorem compression_inner_left (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (x y : V) :
    inner (𝕜 := ℝ) x (operatorCompression A V y) = inner (𝕜 := ℝ) (x : E) (A (y : E)) := by
  exact inner_orthogonalProjection_eq_of_mem_left (K := V) x (A (y : E))

theorem compression_inner_right (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (x y : V) :
    inner (𝕜 := ℝ) (operatorCompression A V x) y = inner (𝕜 := ℝ) (A (x : E)) (y : E) := by
  exact inner_orthogonalProjection_eq_of_mem_right (K := V) y (A (x : E))

theorem compression_symmetric (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (V : Submodule ℝ E) [HasOrthogonalProjection V] :
    (operatorCompression A V).toLinearMap.IsSymmetric := by
  intro x y
  change inner (𝕜 := ℝ) (operatorCompression A V x) y =
    inner (𝕜 := ℝ) x (operatorCompression A V y)
  rw [compression_inner_left,compression_inner_right]
  exact hA x y

theorem compression_bounds (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (a b : ℝ)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) (x : V) :
    a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (operatorCompression A V x) ∧
      inner (𝕜 := ℝ) x (operatorCompression A V x) ≤ b * ‖x‖^2 := by
  rw [compression_inner_left]
  exact hbounds x

theorem compression_quotient (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (x : V) :
    operatorBB1 (operatorCompression A V).toLinearMap x = operatorBB1 A.toLinearMap (x : E) := by
  unfold operatorBB1
  change ‖x‖^2 / inner (𝕜 := ℝ) x (operatorCompression A V x) = _
  rw [compression_inner_left]
  rfl

theorem compression_step (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (α : ℝ) (x : V) (hx : A (x : E) ∈ V) :
    ((operatorGradientStep (operatorCompression A V).toLinearMap α x : V) : E) =
      operatorGradientStep A.toLinearMap α (x : E) := by
  change (x : E) - α • (orthogonalProjection V (A (x : E)) : E) = (x : E)-α • A (x : E)
  rw [orthogonalProjection_eq_self_iff.mpr hx]

def trajectoryGenerators (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ) :
    Fin (N+2) ⊕ Fin (N+2) → E :=
  Sum.elim (fun j => g j) (fun j => A (g j))

def trajectorySpace (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ) : Submodule ℝ E :=
  Submodule.span ℝ (Set.range (trajectoryGenerators A g N))

instance trajectorySpace_finite (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ) :
    FiniteDimensional ℝ (trajectorySpace A g N) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem gradient_mem_trajectorySpace (A : E →L[ℝ] E) (g : ℕ → E) (N j : ℕ) (hj : j < N+2) :
    g j ∈ trajectorySpace A g N :=
  Submodule.subset_span ⟨Sum.inl ⟨j,hj⟩,rfl⟩

theorem image_mem_trajectorySpace (A : E →L[ℝ] E) (g : ℕ → E) (N j : ℕ) (hj : j < N+2) :
    A (g j) ∈ trajectorySpace A g N :=
  Submodule.subset_span ⟨Sum.inr ⟨j,hj⟩,rfl⟩

def compressedTrajectory (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ) :
    ℕ → trajectorySpace A g N :=
  linearBBOrbit (operatorCompression A (trajectorySpace A g N)).toLinearMap
    ⟨g 0,gradient_mem_trajectorySpace A g N 0 (by omega)⟩
    ⟨g 1,gradient_mem_trajectorySpace A g N 1 (by omega)⟩

theorem compressed_trajectory_matches (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    ∀ j, j ≤ N → (compressedTrajectory A g N j : E) = g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ k =>
        have hprev := ih k (by omega) (by omega)
        have hcur := ih (k+1) (by omega) (by omega)
        have hmem : A (compressedTrajectory A g N (k+1) : E) ∈ trajectorySpace A g N := by
          rw [hcur]
          exact image_mem_trajectorySpace A g N (k+1) (by omega)
        change ((operatorGradientStep (operatorCompression A (trajectorySpace A g N)).toLinearMap
            (operatorBB1 (operatorCompression A (trajectorySpace A g N)).toLinearMap
              (compressedTrajectory A g N k)) (compressedTrajectory A g N (k+1)) : trajectorySpace A g N) : E) = g (k+2)
        rw [compression_quotient,hprev,compression_step A (trajectorySpace A g N) _ _ hmem,hcur]
        exact (hupdate k).symm

theorem compressed_trajectory_update (A : E →L[ℝ] E) (g : ℕ → E) (N n : ℕ) :
    compressedTrajectory A g N (n+2) =
      operatorGradientStep (operatorCompression A (trajectorySpace A g N)).toLinearMap
        (operatorBB1 (operatorCompression A (trajectorySpace A g N)).toLinearMap
          (compressedTrajectory A g N n)) (compressedTrajectory A g N (n+1)) := rfl

theorem compressed_trajectory_first (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ) (α₀ : ℝ)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0)) :
    compressedTrajectory A g N 1 =
      operatorGradientStep (operatorCompression A (trajectorySpace A g N)).toLinearMap α₀
        (compressedTrajectory A g N 0) := by
  apply Subtype.ext
  rw [compression_step A (trajectorySpace A g N) α₀ (compressedTrajectory A g N 0)
    (image_mem_trajectorySpace A g N 0 (by omega))]
  exact hfirst

end
end BB
