import BB.HilbertErrorObjective
import BB.OperatorEndpointNorms
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

/-!
# The source's affine quadratic and its centered dynamics

The objective, its actual Fréchet gradient, the centered objective gap and
the gradient update are related by proved identities.  Thus the homogeneous
operator model used by the rate theorems is an exact change of variables.
-/

noncomputable section
namespace BB
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def affineQuadraticGradient (A : E →L[ℝ] E) (b : E) (x : E) : E := A x-b

theorem affine_quadratic_hasGradientAt [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (b x : E) :
    HasGradientAt (affineQuadratic A b) (affineQuadraticGradient A b x) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hq := ((hasFDerivAt_id x).inner ℝ A.hasFDerivAt).const_smul ((1:ℝ)/2)
  have hl := (hasFDerivAt_const b x).inner ℝ (hasFDerivAt_id x)
  convert hq.sub hl using 1
  · funext z
    change inner (𝕜 := ℝ) z (A z)/2-inner (𝕜 := ℝ) b z =
      ((1:ℝ)/2)*inner (𝕜 := ℝ) z (A z)-inner (𝕜 := ℝ) b z
    ring
  ext v
  simp only [affineQuadraticGradient, toDual_apply, inner_sub_left,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply,
    fderivInnerCLM_apply, inner_zero_left, zero_add, smul_eq_mul,id_eq]
  have hs : inner (𝕜 := ℝ) x (A v) = inner (𝕜 := ℝ) (A x) v := (hA x v).symm
  rw [hs,real_inner_comm v (A x)]
  ring

theorem affine_quadratic_gradient_center (A : E →L[ℝ] E) (b a x : E)
    (ha : A a=b) : affineQuadraticGradient A b x = A (x-a) := by
  simp only [affineQuadraticGradient,map_sub,ha]

theorem affine_quadratic_gradient_step (A : E →L[ℝ] E) (b x : E) (α : ℝ) :
    affineQuadraticGradient A b (x-α • affineQuadraticGradient A b x) =
      operatorGradientStep A.toLinearMap α (affineQuadraticGradient A b x) := by
  change A (x-α • (A x-b))-b = (A x-b)-α • A (A x-b)
  rw [map_sub,map_smul]
  abel

theorem affine_quadratic_unique_minimizer (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (b a : E) (ha : A a=b) (m : ℝ) (hm : 0 < m)
    (hlower : ∀ z : E, m*‖z‖^2 ≤ inner (𝕜 := ℝ) z (A z)) :
    ∀ x : E, affineQuadratic A b a ≤ affineQuadratic A b x ∧
      (affineQuadratic A b x=affineQuadratic A b a ↔ x=a) := by
  intro x
  have hg := affine_quadratic_gap A hA b a x ha
  have hb := hlower (x-a)
  have hn : 0 ≤ m*‖x-a‖^2 := mul_nonneg hm.le (sq_nonneg _)
  change affineQuadratic A b x-affineQuadratic A b a = inner (𝕜 := ℝ) (x-a) (A (x-a))/2 at hg
  refine ⟨by linarith,?_⟩
  constructor
  · intro he
    have hnorm : ‖x-a‖^2=0 := by nlinarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  · rintro rfl
    rfl

theorem affine_quadratic_bb1_error_objective_factors (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (m M : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m*‖z‖^2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M*‖z‖^2)
    (b a : E) (ha : A a=b) (x : ℕ → E)
    (hg0 : affineQuadraticGradient A b (x 0) ≠ 0)
    (hupdate : ∀ n, x (n+2)=x (n+1)-operatorBB1 A.toLinearMap
      (affineQuadraticGradient A b (x n)) • affineQuadraticGradient A b (x (n+1))) :
    rootFactor (fun n => ‖x n-a‖/‖x 0-a‖) =
      rootFactor (fun n => ‖affineQuadraticGradient A b (x n)‖/‖affineQuadraticGradient A b (x 0)‖) ∧
      rootFactor (fun n => (affineQuadratic A b (x n)-affineQuadratic A b a)/
        (affineQuadratic A b (x 0)-affineQuadratic A b a)) =
      (rootFactor (fun n => ‖affineQuadraticGradient A b (x n)‖/‖affineQuadraticGradient A b (x 0)‖))^2 := by
  have hgrad (n : ℕ) := affine_quadratic_gradient_center A b a (x n) ha
  have hup (n : ℕ) : affineQuadraticGradient A b (x (n+2)) =
      operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (affineQuadraticGradient A b (x n)))
        (affineQuadraticGradient A b (x (n+1))) := by
    rw [hupdate,affine_quadratic_gradient_step]
  have h := hilbert_bb1_error_objective_factors A hA m M hm hmM hbounds
    (fun n => affineQuadraticGradient A b (x n)) (fun n => x n-a) hg0 hgrad hup
  simpa only [affine_quadratic_gap A hA b a _ ha] using h

end BB
