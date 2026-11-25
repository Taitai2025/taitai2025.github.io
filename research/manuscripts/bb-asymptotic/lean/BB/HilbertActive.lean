import BB.HilbertRates

/-!
# Active invariant subspaces

The sharp upper bound is local to any invariant subspace containing the initial
gradient.  This is the operator form of active spectral reduction.  Identifying
the smallest such spectral interval with the support of a projection-valued
spectral measure is a separate spectral-representation statement.
-/

namespace BB
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def invariantRestriction (A : E →L[ℝ] E) (V : Submodule ℝ E)
    (hV : ∀ x ∈ V, A x ∈ V) : V →L[ℝ] V :=
  (A.comp V.subtypeL).codRestrict V (fun x => hV x x.2)

theorem invariant_restriction_symmetric (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (V : Submodule ℝ E)
    (hV : ∀ x ∈ V, A x ∈ V) : (invariantRestriction A V hV).toLinearMap.IsSymmetric :=
  fun x y => hA (x : E) (y : E)

theorem operator_orbit_in_subspace (A : E →L[ℝ] E) (V : Submodule ℝ E)
    (hV : ∀ x ∈ V, A x ∈ V) (g : ℕ → E) (h0 : g 0 ∈ V) (h1 : g 1 ∈ V)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) : ∀ n, g n ∈ V := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact h0
    | succ n =>
      cases n with
      | zero => exact h1
      | succ k =>
        rw [hupdate k]
        exact V.sub_mem (ih (k+1) (by omega))
          (V.smul_mem _ (hV _ (ih (k+1) (by omega))))

theorem hilbert_invariant_subspace_rootFactor_le (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (V : Submodule ℝ E)
    (hV : ∀ x ∈ V, A x ∈ V) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x ∈ V, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (h0 : g 0 ∈ V) (h1 : g 1 ∈ V)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤ rate a b := by
  let v : ℕ → V := fun n => ⟨g n,operator_orbit_in_subspace A V hV g h0 h1 hupdate n⟩
  let B := invariantRestriction A V hV
  have hv0 : v 0 ≠ 0 := by intro hz; exact hg0 (congrArg Subtype.val hz)
  have hvupdate : ∀ n, v (n+2) = operatorGradientStep B.toLinearMap
      (operatorBB1 B.toLinearMap (v n)) (v (n+1)) := by
    intro n
    apply Subtype.ext
    exact hupdate n
  exact hilbert_normalized_rootFactor_le B (invariant_restriction_symmetric A hA V hV)
    a b ha hab (fun x => hbounds x x.2) v hv0 hvupdate

/-- Only the initial gradient must belong to the invariant subspace: the
actual scalar first step and all delayed updates preserve it. -/
theorem hilbert_active_subspace_rootFactor_le (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (V : Submodule ℝ E)
    (hV : ∀ x ∈ V, A x ∈ V) (a b α₀ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x ∈ V, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (h0 : g 0 ∈ V)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤ rate a b := by
  have h1 : g 1 ∈ V := by
    rw [hfirst]
    exact V.sub_mem h0 (V.smul_mem α₀ (hV _ h0))
  exact hilbert_invariant_subspace_rootFactor_le A hA V hV a b ha hab hbounds g hg0 h0 h1 hupdate

theorem eigenvector_bb1_quotient (H : E →ₗ[ℝ] E) (a : ℝ) (ha : 0 < a)
    (x : E) (hx : x ≠ 0) (heigen : H x = a • x) : operatorBB1 H x = 1/a := by
  have hn : ‖x‖^2 ≠ 0 := ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hx))
  unfold operatorBB1
  rw [heigen,inner_smul_right,real_inner_self_eq_norm_sq]
  field_simp [ha.ne',hn]
  ring

theorem single_eigenvalue_terminates (H : E →ₗ[ℝ] E) (a α₀ : ℝ) (ha : 0 < a)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (heigen : H (g 0) = a • g 0)
    (hfirst : g 1 = operatorGradientStep H α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    g 2 = 0 := by
  have h1 : H (g 1) = a • g 1 := by
    rw [hfirst]
    unfold operatorGradientStep
    rw [map_sub,map_smul,heigen,map_smul,heigen]
    simp only [smul_sub,smul_smul,mul_assoc,mul_left_comm,mul_comm]
  rw [hupdate 0,eigenvector_bb1_quotient H a ha (g 0) hg0 heigen]
  unfold operatorGradientStep
  rw [h1,smul_smul,one_div_mul_cancel ha.ne',one_smul,sub_self]

end
end BB
