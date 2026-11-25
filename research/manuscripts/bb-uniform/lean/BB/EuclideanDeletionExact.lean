import BB.EuclideanGeometry

/-! # The literal endpoint-deletion distance identity

The same orthogonal deletion witness used in the Euclidean recursion has
distance exactly the smaller endpoint norm, as displayed in the source.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean
open Module.End BB.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
  (hn : Fintype.card (Eigenvalues H)=n)

/-- Equation `delete_endpoint`, including its exact equality to the minimum. -/
theorem endpoint_deletion_exact {M : ℝ} {lo hi : Fin n}
    (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi) {z : Pair E}
    (hz : z ∈ stateSet hH hn M lo hi) :
    ∃ z' ∈ stateSet hH hn M lo hi, z'.fst=z.fst ∧ P hH hn lo hi z'=0 ∧
      ‖z'‖≤‖z‖ ∧
      ‖z-z'‖=min ‖sortedCoordinates hH hn z.snd lo‖ ‖sortedCoordinates hH hn z.snd hi‖ ∧
      ‖z-z'‖≤P hH hn lo hi z := by
  have hp := BB.min_le_geometricProduct
    (BB.endpointTheta_pos ha ((sortedLambda_strictMono H hn) hlohi)).le
    (BB.endpointTheta_lt_one ha ((sortedLambda_strictMono H hn) hlohi)).le
    (norm_nonneg (sortedCoordinates hH hn z.snd lo))
    (norm_nonneg (sortedCoordinates hH hn z.snd hi))
  by_cases h : ‖sortedCoordinates hH hn z.snd lo‖≤‖sortedCoordinates hH hn z.snd hi‖
  · refine ⟨eraseState hH hn z lo,eraseState_mem hH hn hz lo,rfl,?_,
      eraseState_norm_le hH hn z lo,?_,?_⟩
    · exact (P_eq_zero_iff hH hn ha hlohi _).mpr (Or.inl (erase_self hH hn z.snd lo))
    · rw [norm_sub_eraseState,min_eq_left h]
    · rw [norm_sub_eraseState]
      simpa only [min_eq_left h] using hp
  · refine ⟨eraseState hH hn z hi,eraseState_mem hH hn hz hi,rfl,?_,
      eraseState_norm_le hH hn z hi,?_,?_⟩
    · exact (P_eq_zero_iff hH hn ha hlohi _).mpr (Or.inr (erase_self hH hn z.snd hi))
    · rw [norm_sub_eraseState,min_eq_right (le_of_not_ge h)]
    · rw [norm_sub_eraseState]
      simpa only [min_eq_right (le_of_not_ge h)] using hp

end BB.Euclidean
