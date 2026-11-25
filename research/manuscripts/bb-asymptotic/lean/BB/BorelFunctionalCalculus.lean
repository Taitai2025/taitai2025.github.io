import BB.BorelQuadratic
import BB.OperatorSpectralMeasure

/-!
# A genuine bounded positive Borel operator

For a bounded positive Borel weight on a compact interval containing the
quadratic-form bounds of A, scalar spectral measures are constructed by Riesz
representation. Their weighted integrals are then polarized and represented by
a bounded operator. Positivity, symmetry and commutation are conclusions.
-/

noncomputable section
namespace BB
open MeasureTheory Set
open scoped Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)
  (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
  (hψbounds : ∀ t, l ≤ ψ t ∧ ψ t ≤ u)

lemma borel_weight_integrable (x : E) :
    Integrable ψ (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  apply bounded_measurable_integrable_finite _ ψ hψ u
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (hl.le.trans (hψbounds t).1)]
  exact (hψbounds t).2

/-- The weighted Borel bilinear form, using only actual constructed scalar measures. -/
def borelWeightBilinear : LinearMap.BilinForm ℝ E :=
  momentBilinear A (operatorSpectralMeasure A hA a b hbounds)
    (operator_spectral_measure_moment A hA a b hbounds) ψ
    (borel_weight_integrable A hA a b hbounds ψ hψ l u hl hψbounds)

variable [CompleteSpace E]

/-- The canonical positive Borel operator Ψ(A), constructed rather than assumed. -/
def borelWeightOperator : E →L[ℝ] E :=
  momentOperator A (operatorSpectralMeasure A hA a b hbounds)
    (operator_spectral_measure_moment A hA a b hbounds) ψ
    (borel_weight_integrable A hA a b hbounds ψ hψ l u hl hψbounds)
    l u hl (hl.le.trans hlu) (fun t => (hψbounds t).1) (fun t => (hψbounds t).2)

theorem borel_weight_operator_inner (x y : E) :
    ⟪borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x, y⟫ =
      borelWeightBilinear A hA a b hbounds ψ hψ l u hl hψbounds x y :=
  momentOperator_inner _ _ _ _ _ _ _ _ _ _ _ x y

/-- This is the defining scalar spectral integral identity for the actual operator. -/
theorem borel_weight_operator_self (x : E) :
    ⟪borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x, x⟫ =
      ∫ t, ψ t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
  momentOperator_self _ _ _ _ _ _ _ _ _ _ _ x

theorem borel_weight_operator_symmetric :
    (borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds).toLinearMap.IsSymmetric :=
  momentOperator_symmetric _ _ _ _ _ _ _ _ _ _ _

theorem borel_weight_operator_bounds (x : E) :
    l * ‖x‖^2 ≤ ⟪x, borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x⟫ ∧
      ⟪x, borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x⟫ ≤ u * ‖x‖^2 :=
  momentOperator_bounds _ _ _ _ _ _ _ _ _ _ _ x

theorem borel_weight_operator_commute :
    Commute (borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds) A :=
  momentOperator_commute _ _ _ _ _ hA _ _ _ _ _ _

/-- Uniqueness of a symmetric bounded operator from its real diagonal form. -/
theorem symmetric_operator_eq_of_diagonal (B C : E →L[ℝ] E)
    (hB : B.toLinearMap.IsSymmetric) (hC : C.toLinearMap.IsSymmetric)
    (h : ∀ x, ⟪B x, x⟫ = ⟪C x, x⟫) : B = C := by
  have hs : (B.toLinearMap - C.toLinearMap).IsSymmetric := by
    intro x y
    simp only [LinearMap.sub_apply, inner_sub_left, inner_sub_right]
    rw [hB x y, hC x y]
  have hz : B.toLinearMap - C.toLinearMap = 0 := hs.inner_map_self_eq_zero.mp (by
    intro x
    change ⟪B x - C x, x⟫ = 0
    rw [inner_sub_left, h x, sub_self])
  have heq := sub_eq_zero.mp hz
  ext x
  exact congrArg (fun L : E →ₗ[ℝ] E => L x) heq

/-- The spectral integral characterization uniquely identifies the constructed operator. -/
theorem borel_weight_operator_unique (B : E →L[ℝ] E)
    (hB : B.toLinearMap.IsSymmetric)
    (hdiag : ∀ x, ⟪B x, x⟫ =
      ∫ t, ψ t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) :
    B = borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds := by
  apply symmetric_operator_eq_of_diagonal B _ hB
    (borel_weight_operator_symmetric A hA a b hbounds ψ hψ l u hl hlu hψbounds)
  intro x
  rw [hdiag x, borel_weight_operator_self]

/-- Existence has only the original operator order bounds and Borel weight bounds as premises. -/
theorem positive_borel_operator_exists :
    ∃ W : E →L[ℝ] E, W.toLinearMap.IsSymmetric ∧ Commute W A ∧
      (∀ x, ⟪W x, x⟫ = ∫ t, ψ t
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) ∧
      (∀ x, l * ‖x‖^2 ≤ ⟪x, W x⟫ ∧ ⟪x, W x⟫ ≤ u * ‖x‖^2) :=
  ⟨borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds,
    borel_weight_operator_symmetric A hA a b hbounds ψ hψ l u hl hlu hψbounds,
    borel_weight_operator_commute A hA a b hbounds ψ hψ l u hl hlu hψbounds,
    borel_weight_operator_self A hA a b hbounds ψ hψ l u hl hlu hψbounds,
    borel_weight_operator_bounds A hA a b hbounds ψ hψ l u hl hlu hψbounds⟩

end BB
