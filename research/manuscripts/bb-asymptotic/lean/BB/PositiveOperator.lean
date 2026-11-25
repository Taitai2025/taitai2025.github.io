import BB.UniversalFinite
import BB.NonlinearTracking

/-! # The nonlinear model inequalities follow from positive selfadjoint bounds -/

namespace BB
noncomputable section
open scoped BigOperators

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finite_operator_square_bounds {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ v : E, a*‖v‖^2 ≤ inner (𝕜 := ℝ) v (H v) ∧
      inner (𝕜 := ℝ) v (H v) ≤ b*‖v‖^2) (x : E) :
    a * inner (𝕜 := ℝ) x (H x) ≤ ‖H x‖^2 ∧
      ‖H x‖^2 ≤ b * inner (𝕜 := ℝ) x (H x) := by
  have hlam := eigenvalue_bounds hH a b hbounds
  have hnorm : ‖H x‖^2 = ∑ i, (eigenValues hH i)^2 * (eigenCoordinates hH x i)^2 := by
    rw [← eigen_coordinates_energy hH (H x)]
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    rw [eigen_coordinates_apply,mul_pow]
  rw [eigen_coordinates_inner,hnorm]
  constructor
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : a*eigenValues hH i ≤ (eigenValues hH i)^2 := by
      nlinarith [(hlam i).1]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hi (sq_nonneg (eigenCoordinates hH x i))
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hi : (eigenValues hH i)^2 ≤ b*eigenValues hH i := by
      nlinarith [(hlam i).1,(hlam i).2]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hi (sq_nonneg (eigenCoordinates hH x i))

end Finite

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem operator_square_bounds_via_compression (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (x : E) :
    a * inner (𝕜 := ℝ) x (A x) ≤ ‖A x‖^2 ∧
      ‖A x‖^2 ≤ b * inner (𝕜 := ℝ) x (A x) := by
  let g : ℕ → E := fun _ => x
  let V := trajectorySpace A g 0
  let v : V := ⟨x,gradient_mem_trajectorySpace A g 0 0 (by omega)⟩
  have hAv : A (v : E) ∈ V := image_mem_trajectorySpace A g 0 0 (by omega)
  have he : (operatorCompression A V v : E) = A x := orthogonalProjection_eq_self_iff.mpr hAv
  have h := finite_operator_square_bounds (compression_symmetric A hA V) a b ha
    (compression_bounds A V a b hbounds) v
  change a*inner (𝕜 := ℝ) v (operatorCompression A V v) ≤ ‖operatorCompression A V v‖^2 ∧
    ‖operatorCompression A V v‖^2 ≤ b*inner (𝕜 := ℝ) v (operatorCompression A V v) at h
  rw [compression_inner_left] at h
  change a*inner (𝕜 := ℝ) x (A x) ≤ ‖(operatorCompression A V v : E)‖^2 ∧
    ‖(operatorCompression A V v : E)‖^2 ≤ b*inner (𝕜 := ℝ) x (A x) at h
  simpa only [he] using h

/-- All five quantitative model properties are derived from the stated
selfadjoint positive bounds, for arbitrary real Hilbert spaces. -/
theorem positiveModel_of_order_bounds (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ x : E, m*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ M*‖x‖^2) : Nonlinear.PositiveModel A m M := by
  exact ⟨hm,hmM,
    (fun x => (operator_norm_bounds_via_compression A hA m M hm hmM hbounds x).2),
    (fun x => (hbounds x).1),
    (fun x => (operator_square_bounds_via_compression A hA m M hm hbounds x).1),
    (fun x => (operator_square_bounds_via_compression A hA m M hm hbounds x).2)⟩

end General
end
end BB
