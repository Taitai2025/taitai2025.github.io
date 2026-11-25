import BB.QuadraticAffine
import BB.OperatorFaceStep

/-! # The baseline endpoint Lyapunov function in actual quadratic error coordinates

This identifies the homogeneous endpoint energy with the original affine
quadratic objective's error form.  The projectors are actual orthogonal
spectral coordinates of H, and the gradient is that of the same objective.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Operator
open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def endpointGradientEnergy {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) (g : E) : ℝ :=
  (BB.geometricProduct (BB.endpointTheta (lo : ℝ) (hi : ℝ))
    ‖coordinates hH g lo‖ ‖coordinates hH g hi‖)^2

theorem endpointGradientEnergy_expanded {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ)) (g : E) :
    endpointGradientEnergy hH lo hi g =
      ‖coordinates hH g lo‖^(2*(hi : ℝ)/((lo : ℝ)+(hi : ℝ))) *
        ‖coordinates hH g hi‖^(2*(lo : ℝ)/((lo : ℝ)+(hi : ℝ))) := by
  unfold endpointGradientEnergy
  rw [BB.geometricProduct_square (norm_nonneg _) (norm_nonneg _),BB.endpoint_complement ha hab]
  simp only [BB.endpointTheta,mul_div_assoc]

theorem endpointGradientEnergy_homogeneous {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    (g : E) {t : ℝ} (ht : 0 ≤ t) :
    endpointGradientEnergy hH lo hi (t • g)=t^2*endpointGradientEnergy hH lo hi g := by
  unfold endpointGradientEnergy
  have hc (mu : Eigenvalues H) : coordinates hH (t • g) mu=t • coordinates hH g mu := by
    simp [coordinates]
  rw [hc,hc,norm_smul,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,
    BB.geometricProduct_homogeneous (BB.endpointTheta_pos ha hab).le
      (BB.endpointTheta_lt_one ha hab).le ht (norm_nonneg _) (norm_nonneg _)]
  ring

theorem coordinate_H_norm {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (mu : Eigenvalues H) (hmu : 0 ≤ (mu : ℝ)) (e : E) :
    ‖coordinates hH (H e) mu‖=(mu : ℝ)*‖coordinates hH e mu‖ := by
  unfold coordinates
  rw [hH.diagonalization_apply_self_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hmu]

/-- The squared energy is two-homogeneous for every real scalar, including
negative scalars; the endpoint norms remove its sign. -/
theorem endpointGradientEnergy_smul {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    (g : E) (t : ℝ) :
    endpointGradientEnergy hH lo hi (t • g)=t^2*endpointGradientEnergy hH lo hi g := by
  have heq : endpointGradientEnergy hH lo hi (t • g)=
      endpointGradientEnergy hH lo hi (|t| • g) := by
    simp [endpointGradientEnergy,coordinates,norm_smul,Real.norm_eq_abs,abs_abs]
  rw [heq,endpointGradientEnergy_homogeneous hH ha hab g (abs_nonneg t),sq_abs]

theorem endpointGradientEnergy_error_form {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ)) (e : E) :
    endpointGradientEnergy hH lo hi (H e) =
      (lo : ℝ)^(2*(hi : ℝ)/((lo : ℝ)+(hi : ℝ))) *
      (hi : ℝ)^(2*(lo : ℝ)/((lo : ℝ)+(hi : ℝ))) *
      ‖coordinates hH e lo‖^(2*(hi : ℝ)/((lo : ℝ)+(hi : ℝ))) *
      ‖coordinates hH e hi‖^(2*(lo : ℝ)/((lo : ℝ)+(hi : ℝ))) := by
  rw [endpointGradientEnergy_expanded hH ha hab]
  rw [coordinate_H_norm hH lo ha.le,coordinate_H_norm hH hi (ha.trans hab).le,
    Real.mul_rpow ha.le (norm_nonneg _),Real.mul_rpow (ha.trans hab).le (norm_nonneg _)]
  ring

theorem affine_endpoint_energy_error_form [CompleteSpace E]
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (d p x : E) (hp : H p=d) {lo hi : Eigenvalues H.toLinearMap}
    (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ)) :
    endpointGradientEnergy hH lo hi (gradient (BB.Quadratic.affineObjective H d) x) =
      (lo : ℝ)^(2*(hi : ℝ)/((lo : ℝ)+(hi : ℝ))) *
      (hi : ℝ)^(2*(lo : ℝ)/((lo : ℝ)+(hi : ℝ))) *
      ‖coordinates hH (x-p) lo‖^(2*(hi : ℝ)/((lo : ℝ)+(hi : ℝ))) *
      ‖coordinates hH (x-p) hi‖^(2*(lo : ℝ)/((lo : ℝ)+(hi : ℝ))) := by
  rw [BB.Quadratic.affineObjective_gradient_error H hH hp x]
  exact endpointGradientEnergy_error_form hH ha hab (x-p)

end BB.Operator
