import BB.OperatorCondition
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false

noncomputable section
namespace BB.Quadratic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def objective (H : E →L[ℝ] E) (x : E) : ℝ := (1/2:ℝ)*@inner ℝ _ _ x (H x)

/-- The quadratic for a prescribed continuous Hessian is smooth of every order. -/
theorem objective_contDiff (H : E →L[ℝ] E) (n : ℕ∞) : ContDiff ℝ n (objective H) :=
  contDiff_const.mul (contDiff_id.inner ℝ H.contDiff)

/-- A symmetric operator is the actual gradient of its quadratic form. -/
theorem objective_hasGradientAt (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) (x : E) :
    HasGradientAt (objective H) (H x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hh := ((hasFDerivAt_id x).inner ℝ H.hasFDerivAt).const_mul (1/2:ℝ)
  convert hh using 1
  ext y
  simp only [ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply,ContinuousLinearMap.id_apply,fderivInnerCLM_apply,
    InnerProductSpace.toDual_apply,smul_eq_mul,id_eq]
  have hsym := hH x y
  change @inner ℝ _ _ (H x) y = @inner ℝ _ _ x (H y) at hsym
  rw [← hsym,real_inner_comm y (H x)]
  ring

theorem objective_gradient (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) :
    gradient (objective H) = H :=
  gradient_eq (objective_hasGradientAt H hH)

/-- The derivative of the gradient is the prescribed operator at every point. -/
theorem objective_hessian (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) (x : E) :
    fderiv ℝ (gradient (objective H)) x = H := by
  rw [objective_gradient H hH]
  exact H.fderiv

@[simp] theorem objective_zero (H : E →L[ℝ] E) : objective H 0 = 0 := by simp [objective]

theorem objective_pos (H : E →L[ℝ] E)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x)) {x : E} (hx : x ≠ 0) :
    0 < objective H x := mul_pos (by norm_num) (hpd x hx)

section FiniteDimensional
variable [FiniteDimensional ℝ E]
open Module.End BB.Operator
open scoped BigOperators

/-- The squared gradient norm is the actual second spectral moment. -/
theorem hessian_sq_norm_spectral (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric) (x : E) :
    ‖H x‖^2 = ∑ mu : Eigenvalues H.toLinearMap,
      (mu:ℝ)^2*‖coordinates hH x mu‖^2 := by
  rw [← coordinates_sq_norm hH (H x)]
  apply Finset.sum_congr rfl
  intro mu _
  unfold coordinates
  have heig : hH.diagonalization (H x) mu = (mu:ℝ) • hH.diagonalization x mu :=
    hH.diagonalization_apply_self_apply x mu
  rw [heig,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

/-- Exact quadratic gap comparison in the original Hilbert-space norm, derived
from the true spectral decomposition of the prescribed operator. -/
theorem objective_gap_of_spectral_bounds (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ mu : Eigenvalues H.toLinearMap, a ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ b) (x : E) :
    (1/(2*b))*‖H x‖^2 ≤ objective H x ∧ objective H x ≤ (1/(2*a))*‖H x‖^2 := by
  have hb : 0 < b := ha.trans_le hab
  have hform : @inner ℝ _ _ x (H x) = ∑ mu : Eigenvalues H.toLinearMap,
      (mu:ℝ)*‖coordinates hH x mu‖^2 := quadratic_form_spectral hH x
  have hlo : a*@inner ℝ _ _ x (H x) ≤ ‖H x‖^2 := by
    rw [hform,hessian_sq_norm_spectral H hH,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro mu _
    have hmu : 0 ≤ (mu:ℝ) := ha.le.trans (hspec mu).1
    have hh := mul_le_mul_of_nonneg_right (hspec mu).1 hmu
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖coordinates hH x mu‖)
    nlinarith only [hh']
  have hhi : ‖H x‖^2 ≤ b*@inner ℝ _ _ x (H x) := by
    rw [hform,hessian_sq_norm_spectral H hH,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro mu _
    have hmu : 0 ≤ (mu:ℝ) := ha.le.trans (hspec mu).1
    have hh := mul_le_mul_of_nonneg_right (hspec mu).2 hmu
    have hh' := mul_le_mul_of_nonneg_right hh (sq_nonneg ‖coordinates hH x mu‖)
    nlinarith only [hh']
  unfold objective
  constructor
  · rw [show (1/(2*b))*‖H x‖^2 = ‖H x‖^2/(2*b) by ring]
    apply (div_le_iff (mul_pos (by norm_num : (0 : ℝ) < 2) hb)).mpr
    nlinarith only [hhi]
  · rw [show (1/(2*a))*‖H x‖^2 = ‖H x‖^2/(2*a) by ring]
    apply (le_div_iff (mul_pos (by norm_num : (0 : ℝ) < 2) ha)).mpr
    nlinarith only [hlo]

/-- The same comparison written entirely with the genuine objective and gradient. -/
theorem actual_quadratic_gap (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ mu : Eigenvalues H.toLinearMap, a ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ b) (x : E) :
    (1/(2*b))*‖gradient (objective H) x‖^2 ≤ objective H x-objective H 0 ∧
      objective H x-objective H 0 ≤ (1/(2*a))*‖gradient (objective H) x‖^2 := by
  rw [objective_gradient H hH,objective_zero,sub_zero]
  exact objective_gap_of_spectral_bounds H hH ha hab hspec x

end FiniteDimensional

end BB.Quadratic
