import BB.BorelConjugacy
import BB.PositiveSquareRoot

/-!
# Signed bounded Borel operators from actual scalar spectral measures

A bounded measurable real function is shifted by an explicit positive constant,
constructed by the already proved positive Borel procedure, then shifted back.
The resulting operator is symmetric, commutes with A, has the exact scalar
integral form, and has the expected square-density spectral measure.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)

lemma operator_spectral_integral_one (x : E) :
    (∫ _t : Icc a b, (1 : ℝ) ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) =
      ‖x‖^2 := by
  simpa only [pow_zero, Function.iterate_zero_apply, real_inner_self_eq_norm_sq] using
    operator_spectral_measure_moment A hA a b hbounds x 0

section PositiveSquare
variable (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) (hψbounds : ∀ t, l ≤ ψ t ∧ ψ t ≤ u)

lemma borel_weight_square_integrable (x : E) :
    Integrable (fun t => (ψ t)^2) (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  apply bounded_measurable_integrable_finite _ _ ((continuous_pow 2).measurable.comp hψ) (u^2)
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left (hl.le.trans (hψbounds t).1) (hψbounds t).2 2

/-- Applying the positive Borel operator multiplies every scalar spectral measure by ψ². -/
theorem borel_weight_operator_scalar_measure (x : E) :
    operatorSpectralMeasure A hA a b hbounds
      (borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x) =
      finiteDensity (operatorSpectralMeasure A hA a b hbounds x) (fun t => (ψ t)^2)
        (borel_weight_square_integrable A hA a b hbounds ψ hψ l u hl hψbounds x) := by
  let W := borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds
  obtain ⟨S, hS, hsq, _hform, _hnorm, _hunit, hcommAll⟩ :=
    positive_operator_square_root_exists W
      (borel_weight_operator_symmetric A hA a b hbounds ψ hψ l u hl hlu hψbounds)
      l u hl hlu (borel_weight_operator_bounds A hA a b hbounds ψ hψ l u hl hlu hψbounds)
  have hcomm : ∀ z, S (A z) = A (S z) := by
    apply hcommAll A
    intro z
    exact congrArg (fun T : E →L[ℝ] E => T z)
      (borel_weight_operator_commute A hA a b hbounds ψ hψ l u hl hlu hψbounds).eq
  have hx : W x = S (S x) := congrArg (fun T : E →L[ℝ] E => T x) hsq
  change operatorSpectralMeasure A hA a b hbounds (W x) = _
  rw [hx, borel_square_root_scalar_measure A hA a b hbounds ψ hψ l u hl hlu hψbounds
    S hS hsq hcomm (S x)]
  apply Subtype.ext
  change (operatorSpectralMeasure A hA a b hbounds (S x) : Measure (Icc a b)).withDensity
      (fun t => ENNReal.ofReal (ψ t)) = _
  rw [borel_square_root_scalar_measure A hA a b hbounds ψ hψ l u hl hlu hψbounds S hS hsq hcomm x]
  change ((operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)).withDensity
      (fun t => ENNReal.ofReal (ψ t))).withDensity (fun t => ENNReal.ofReal (ψ t)) =
    (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)).withDensity
      (fun t => ENNReal.ofReal ((ψ t)^2))
  rw [← withDensity_mul _ hψ.ennreal_ofReal hψ.ennreal_ofReal]
  congr 1
  funext t
  simp only [Pi.mul_apply, pow_two, ENNReal.ofReal_mul (hl.le.trans (hψbounds t).1)]

/-- The actual norm-square spectral integral of a positive Borel operator. -/
theorem borel_weight_operator_norm_sq (x : E) :
    ‖borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x‖^2 =
      ∫ t, (ψ t)^2 ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [← operator_spectral_integral_one A hA a b hbounds,
    borel_weight_operator_scalar_measure A hA a b hbounds ψ hψ l u hl hlu hψbounds]
  rw [finiteDensity_integral _ (fun t => (ψ t)^2) _
    ((continuous_pow 2).measurable.comp hψ) (fun t => sq_nonneg (ψ t))]
  simp only [mul_one]

end PositiveSquare

/-- A uniformly positive shift of a bounded real Borel function. -/
def shiftedBorelWeight (φ : Icc a b → ℝ) (C : ℝ) : Icc a b → ℝ := fun t => φ t + (C+1)

lemma shiftedBorelWeight_measurable (φ : Icc a b → ℝ) (hφ : Measurable φ) (C : ℝ) :
    Measurable (shiftedBorelWeight a b φ C) := hφ.add measurable_const

lemma shiftedBorelWeight_bounds (φ : Icc a b → ℝ) (C : ℝ)
    (hφC : ∀ t, |φ t| ≤ C) (t : Icc a b) :
    1 ≤ shiftedBorelWeight a b φ C t ∧ shiftedBorelWeight a b φ C t ≤ 2*C+1 := by
  have h := abs_le.mp (hφC t)
  dsimp [shiftedBorelWeight]
  constructor <;> linarith only [h.1, h.2]

variable (φ : Icc a b → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : 0 ≤ C)
  (hφC : ∀ t, |φ t| ≤ C)

/-- Genuine bounded signed Borel calculus, constructed by a positive shift. -/
def borelOperator : E →L[ℝ] E :=
  borelWeightOperator A hA a b hbounds (shiftedBorelWeight a b φ C)
    (shiftedBorelWeight_measurable a b φ hφ C) 1 (2*C+1) (by norm_num) (by linarith only [hC])
    (shiftedBorelWeight_bounds a b φ C hφC) - (C+1) • (1 : E →L[ℝ] E)

lemma borel_integrable (x : E) :
    Integrable φ (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
  bounded_measurable_integrable_finite _ φ hφ C (fun t => by simpa only [Real.norm_eq_abs] using hφC t)

lemma borel_square_integrable (x : E) :
    Integrable (fun t => (φ t)^2) (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  apply bounded_measurable_integrable_finite _ _ ((continuous_pow 2).measurable.comp hφ) (C^2)
  intro t
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    (φ t)^2 = |φ t|^2 := (sq_abs _).symm
    _ ≤ C^2 := pow_le_pow_left (abs_nonneg _) (hφC t) 2

/-- Exact scalar integral identity for every bounded measurable signed real function. -/
theorem borel_operator_self (x : E) :
    ⟪borelOperator A hA a b hbounds φ hφ C hC hφC x, x⟫ =
      ∫ t, φ t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [borelOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, real_inner_smul_left, borel_weight_operator_self,
    real_inner_self_eq_norm_sq]
  change (∫ t, φ t + (C+1) ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) - _ = _
  rw [integral_add (borel_integrable A hA a b hbounds φ hφ C hφC x) (integrable_const _)]
  have hi : (∫ _t : Icc a b, C+1 ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) =
      (C+1)*‖x‖^2 := by
    calc
      _ = ∫ _t : Icc a b, (C+1)*1 ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by simp
      _ = (C+1)*‖x‖^2 := by rw [integral_mul_left, operator_spectral_integral_one]
  rw [hi]
  ring

theorem borel_operator_symmetric :
    (borelOperator A hA a b hbounds φ hφ C hC hφC).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪borelOperator A hA a b hbounds φ hφ C hC hφC x, y⟫ =
    ⟪x, borelOperator A hA a b hbounds φ hφ C hC hφC y⟫
  simp only [borelOperator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, inner_sub_left, inner_sub_right, real_inner_smul_left, inner_smul_right]
  congr 1
  exact borel_weight_operator_symmetric _ _ _ _ _ _ _ _ _ _ _ _ x y

theorem borel_operator_commute : Commute (borelOperator A hA a b hbounds φ hφ C hC hφC) A := by
  unfold borelOperator
  apply Commute.sub_left
  · exact borel_weight_operator_commute A hA a b hbounds (shiftedBorelWeight a b φ C)
      (shiftedBorelWeight_measurable a b φ hφ C) 1 (2*C+1) (by norm_num)
      (by linarith only [hC]) (shiftedBorelWeight_bounds a b φ C hφC)
  · change ((C+1) • (1 : E →L[ℝ] E)) * A = A * ((C+1) • (1 : E →L[ℝ] E))
    apply ContinuousLinearMap.ext
    intro x
    change (C+1) • (A x) = A ((C+1) • x)
    exact (A.map_smul (C+1) x).symm

end BB
