import BB.GradientDynamics
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# Orthogonal spectral coordinates of the actual linear BB algorithm

The diagonal model is obtained from mathlib's finite-dimensional spectral
theorem.  The coordinate map is an isometry, and both the quotient and every
gradient update are proved to commute with it.
-/

namespace BB
noncomputable section
open scoped BigOperators
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def operatorBB1 (H : E →ₗ[ℝ] E) (g : E) : ℝ :=
  ‖g‖ ^ 2 / ⟪g, H g⟫

def operatorGradientStep (H : E →ₗ[ℝ] E) (α : ℝ) (g : E) : E :=
  g - α • H g

def eigenCoordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) :
    Fin (FiniteDimensional.finrank ℝ E) → ℝ :=
  fun i => (hH.eigenvectorBasis rfl).repr g i

def eigenValues {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) :
    Fin (FiniteDimensional.finrank ℝ E) → ℝ := hH.eigenvalues rfl

def fromEigenCoordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (v : Fin (FiniteDimensional.finrank ℝ E) → ℝ) : E :=
  (hH.eigenvectorBasis rfl).repr.symm ((WithLp.equiv 2 _).symm v)

theorem eigen_coordinates_from {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (v : Fin (FiniteDimensional.finrank ℝ E) → ℝ) :
    eigenCoordinates hH (fromEigenCoordinates hH v) = v := by
  funext i
  simp only [eigenCoordinates,fromEigenCoordinates,LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem eigen_coordinates_injective {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) :
    Function.Injective (eigenCoordinates hH) := by
  intro v w h
  apply (hH.eigenvectorBasis rfl).repr.injective
  ext i
  exact congrFun h i

theorem eigen_coordinates_norm {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) :
    normDiag (eigenCoordinates hH g) = ‖g‖ := by
  change normDiag (fun i => (hH.eigenvectorBasis rfl).repr g i) = ‖g‖
  rw [normDiag_eq_euclidean_norm, LinearIsometryEquiv.norm_map]

theorem eigen_coordinates_energy {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) :
    energy (eigenCoordinates hH g) = ‖g‖ ^ 2 := by
  have he : 0 ≤ energy (eigenCoordinates hH g) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn := congrArg (fun x : ℝ => x ^ 2) (eigen_coordinates_norm hH g)
  simpa only [normDiag,Real.sq_sqrt he] using hn

theorem eigen_coordinates_apply {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (g : E) (i : Fin (FiniteDimensional.finrank ℝ E)) :
    eigenCoordinates hH (H g) i = eigenValues hH i * eigenCoordinates hH g i :=
  hH.eigenvectorBasis_apply_self_apply rfl g i

theorem eigen_coordinates_inner {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) :
    ⟪g, H g⟫ = ∑ i, eigenValues hH i * (eigenCoordinates hH g i)^2 := by
  rw [← (hH.eigenvectorBasis rfl).repr.inner_map_map g (H g),PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (eigenCoordinates hH g i) * (eigenCoordinates hH (H g) i) = _
  rw [eigen_coordinates_apply]
  ring

theorem eigen_coordinates_quotient {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) :
    operatorBB1 H g = diagonalBB1 (eigenValues hH) (eigenCoordinates hH g) := by
  unfold operatorBB1 diagonalBB1
  rw [eigen_coordinates_energy,eigen_coordinates_inner]

theorem eigen_coordinates_update {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (α : ℝ) (g : E) :
    eigenCoordinates hH (operatorGradientStep H α g) =
      gradientUpdate (eigenValues hH) α (eigenCoordinates hH g) := by
  funext i
  change (hH.eigenvectorBasis rfl).repr (g-α • H g) i = _
  rw [map_sub,map_smul]
  change eigenCoordinates hH g i - α * eigenCoordinates hH (H g) i = _
  rw [eigen_coordinates_apply]
  unfold gradientUpdate
  ring

theorem eigen_coordinates_delayed_orbit {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (g : ℕ → E)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    ∀ n, eigenCoordinates hH (g (n+2)) =
      gradientUpdate (eigenValues hH) (diagonalBB1 (eigenValues hH)
        (eigenCoordinates hH (g n))) (eigenCoordinates hH (g (n+1))) := by
  intro n
  rw [hupdate n,eigen_coordinates_update,eigen_coordinates_quotient]

theorem eigenvalue_bounds {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ v : E, a * ‖v‖^2 ≤ ⟪v, H v⟫ ∧
      ⟪v, H v⟫ ≤ b * ‖v‖^2)
    (i : Fin (FiniteDimensional.finrank ℝ E)) :
    a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b := by
  have hv := hbounds (hH.eigenvectorBasis rfl i)
  have hn : ‖hH.eigenvectorBasis rfl i‖ = 1 :=
    (hH.eigenvectorBasis rfl).orthonormal.1 i
  rw [hH.apply_eigenvectorBasis rfl i,inner_smul_right,real_inner_self_eq_norm_sq,hn] at hv
  simpa only [one_pow,mul_one] using hv

theorem eigen_coordinates_rootFactor {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (g : ℕ → E) :
    rootFactor (fun n => normDiag (eigenCoordinates hH (g n))) =
      rootFactor (fun n => ‖g n‖) := by
  congr 1
  funext n
  exact eigen_coordinates_norm hH (g n)

end
end BB
