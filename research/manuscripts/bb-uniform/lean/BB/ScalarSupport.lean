import BB.StateLipschitz

set_option autoImplicit false

namespace BB.Spectral
variable {ι : Type*} [Fintype ι]

@[simp] theorem stateMap_zero_current (lam w u : ι → ℝ) :
    stateMap lam w (u,0) = 0 := by
  ext i <;> simp [stateMap,diagonalStep]

/-- A missing current component disappears from both entries after one update. -/
theorem stateMap_component_zero (lam w : ι → ℝ) (z : State ι) (i : ι)
    (hz : z.2 i = 0) :
    (stateMap lam w z).1 i = 0 ∧ (stateMap lam w z).2 i = 0 := by
  simp [stateMap,diagonalStep,hz]

/-- A common coordinate support is invariant under every weight. -/
theorem stateMap_preserves_support (lam w : ι → ℝ) (z : State ι) (S : Set ι)
    (hz : ∀ i, i ∉ S → z.1 i = 0 ∧ z.2 i = 0) :
    ∀ i, i ∉ S → (stateMap lam w z).1 i = 0 ∧ (stateMap lam w z).2 i = 0 := by
  intro i hi
  exact stateMap_component_zero lam w z i (hz i hi).2

/-- A one-eigenvalue spectral support forces the reciprocal-eigenvalue step. -/
theorem vectorAlpha_single_eigenvalue {lam w u : ι → ℝ} {a : ℝ}
    (ha : 0 < a) (hw : ∀ i, 1 ≤ w i)
    (hsupport : ∀ i, u i = 0 ∨ lam i = a) (hu : u ≠ 0) :
    vectorAlpha lam w u = 1/a := by
  have hs : ∀ i, u i = 0 ∨ (a ≤ lam i ∧ lam i ≤ a) := by
    intro i
    rcases hsupport i with hzero | heq
    · exact Or.inl hzero
    · exact Or.inr ⟨heq.symm.le,heq.le⟩
  have hh := vectorAlpha_bounds_on_support ha (le_refl a) hw hs hu
  exact le_antisymm hh.2 hh.1

/-- The exact base case of the induction: one update kills the current vector. -/
theorem stateMap_single_eigenvalue {lam w : ι → ℝ} {a M : ℝ}
    (ha : 0 < a) (hw : ∀ i, 1 ≤ w i) {z : State ι} (hz : Cone M z)
    (hu : ∀ i, z.1 i = 0 ∨ lam i = a) (hv : ∀ i, z.2 i = 0 ∨ lam i = a) :
    stateMap lam w z = (z.2,0) := by
  by_cases hzero : z.1 = 0
  · have hstate := cone_eq_zero_of_fst hz hzero
    subst z
    change stateMap lam w 0 = (0,0)
    rw [stateMap_zero]
    rfl
  · have hα := vectorAlpha_single_eigenvalue ha hw hu hzero
    apply Prod.ext
    · rfl
    · funext i
      change (1-vectorAlpha lam w z.1*lam i)*z.2 i = 0
      rw [hα]
      rcases hv i with hz | hl
      · simp [hz]
      · rw [hl]
        simp [ne_of_gt ha]

/-- Any two successive maps terminate a one-eigenvalue supported admissible state. -/
theorem two_updates_single_eigenvalue {lam w w' : ι → ℝ} {a M : ℝ}
    (ha : 0 < a) (hw : ∀ i, 1 ≤ w i) {z : State ι} (hz : Cone M z)
    (hu : ∀ i, z.1 i = 0 ∨ lam i = a) (hv : ∀ i, z.2 i = 0 ∨ lam i = a) :
    stateMap lam w' (stateMap lam w z) = 0 := by
  rw [stateMap_single_eigenvalue ha hw hz hu hv]
  exact stateMap_zero_current lam w' z.2

/-- Scalar multiplication preserves the cone. -/
theorem cone_smul {M : ℝ} {z : State ι} (hz : Cone M z) (t : ℝ) : Cone M (t • z) := by
  unfold Cone at *
  change ‖t • z.2‖ ≤ M * ‖t • z.1‖
  rw [norm_smul,norm_smul]
  nlinarith only [mul_le_mul_of_nonneg_left hz (norm_nonneg t)]

end BB.Spectral
