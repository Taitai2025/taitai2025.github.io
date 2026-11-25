import BB.BorelSigned

/-!
# Exact square-density and norm identities for signed Borel operators

The proof expands actual operator moments after the positive shift and uses
finite-measure moment uniqueness. No multiplicative Borel calculus is assumed.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology Polynomial
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma operator_iterate_sub (A : E →L[ℝ] E) (x y : E) (k : ℕ) :
    (A : E → E)^[k] (x-y) = (A : E → E)^[k] x - (A : E → E)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, map_sub,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)
  (φ : Icc a b → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : 0 ≤ C)
  (hφC : ∀ t, |φ t| ≤ C)

/-- Exact scalar spectral measures for every bounded signed Borel multiplier. -/
theorem borel_operator_scalar_measure (x : E) :
    operatorSpectralMeasure A hA a b hbounds (borelOperator A hA a b hbounds φ hφ C hC hφC x) =
      finiteDensity (operatorSpectralMeasure A hA a b hbounds x) (fun t => (φ t)^2)
        (borel_square_integrable A hA a b hbounds φ hφ C hφC x) := by
  let ψ := shiftedBorelWeight a b φ C
  have hψ : Measurable ψ := shiftedBorelWeight_measurable a b φ hφ C
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hu : (1 : ℝ) ≤ 2*C+1 := by linarith only [hC]
  have hψb : ∀ t, 1 ≤ ψ t ∧ ψ t ≤ 2*C+1 := shiftedBorelWeight_bounds a b φ C hφC
  let W := borelWeightOperator A hA a b hbounds ψ hψ 1 (2*C+1) h1 hu hψb
  have hF : borelOperator A hA a b hbounds φ hφ C hC hφC x = W x - (C+1) • x := rfl
  apply finite_measure_eq_of_moments a b
  intro k
  rw [operator_spectral_measure_moment, finiteDensity_integral _ (fun t => (φ t)^2) _
    ((continuous_pow 2).measurable.comp hφ) (fun t => sq_nonneg (φ t))]
  have hWk : ⟪W x, (A : E → E)^[k] (W x)⟫ =
      ∫ t, (ψ t)^2 * (t : ℝ)^k
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
    rw [← operator_spectral_measure_moment A hA a b hbounds (W x) k]
    change (∫ t, (t : ℝ)^k ∂(operatorSpectralMeasure A hA a b hbounds
      (borelWeightOperator A hA a b hbounds ψ hψ 1 (2*C+1) h1 hu hψb x) : Measure (Icc a b))) = _
    rw [borel_weight_operator_scalar_measure A hA a b hbounds ψ hψ 1 (2*C+1) h1 hu hψb]
    exact finiteDensity_integral _ (fun t => (ψ t)^2) _
      ((continuous_pow 2).measurable.comp hψ) (fun t => sq_nonneg (ψ t)) _
  have hcross : ⟪x, (A : E → E)^[k] (W x)⟫ = ⟪W x, (A : E → E)^[k] x⟫ := by
    calc
      _ = ⟪(A : E → E)^[k] x, W x⟫ := (operator_iterate_symmetric A hA k x (W x)).symm
      _ = _ := real_inner_comm _ _
  have hmix := borel_weight_operator_power_inner A hA a b hbounds ψ hψ 1 (2*C+1) h1 hu hψb x k
  change ⟪W x, (A : E → E)^[k] x⟫ = _ at hmix
  have hi0 : Integrable (fun t : Icc a b => (t : ℝ)^k)
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
    continuous_integrable_finite _ ⟨_, continuous_subtype_val.pow k⟩
  have hi1 : Integrable (fun t : Icc a b => (t : ℝ)^k * ψ t)
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
    continuous_mul_integrable _ ⟨_, continuous_subtype_val.pow k⟩ ψ
      (borel_weight_integrable A hA a b hbounds ψ hψ 1 (2*C+1) h1 hψb x)
  have hi2 : Integrable (fun t : Icc a b => (ψ t)^2 * (t : ℝ)^k)
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
    have hi := continuous_mul_integrable
      (operatorSpectralMeasure A hA a b hbounds x) ⟨_, continuous_subtype_val.pow k⟩ (fun t => (ψ t)^2)
      (borel_weight_square_integrable A hA a b hbounds ψ hψ 1 (2*C+1) h1 hψb x)
    change Integrable (fun t : Icc a b => (t : ℝ)^k * (ψ t)^2)
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) at hi
    simpa only [mul_comm] using hi
  have halg : (∫ t, (φ t)^2 * (t : ℝ)^k
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) =
      (∫ t, (ψ t)^2 * (t : ℝ)^k ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) -
      (2*(C+1)) * (∫ t, (t : ℝ)^k * ψ t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) +
      (C+1)^2 * (∫ t : Icc a b, (t : ℝ)^k ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) := by
    have hp : (fun t : Icc a b => (φ t)^2 * (t : ℝ)^k) =
        fun t => (ψ t)^2 * (t : ℝ)^k - (2*(C+1)) * ((t : ℝ)^k * ψ t) + (C+1)^2 * (t : ℝ)^k := by
      funext t
      dsimp [ψ, shiftedBorelWeight]
      ring
    have hadd := integral_add (hi2.sub (hi1.const_mul (2*(C+1)))) (hi0.const_mul ((C+1)^2))
    have hsub := integral_sub hi2 (hi1.const_mul (2*(C+1)))
    simp only [Pi.sub_apply] at hadd hsub
    rw [hp, hadd, hsub, integral_mul_left, integral_mul_left]
  rw [hF, operator_iterate_sub, operator_iterate_smul]
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [hcross, hWk, hmix, halg, operator_spectral_measure_moment]
  ring

/-- The precise L² scalar spectral norm formula for bounded real Borel functions. -/
theorem borel_operator_norm_sq (x : E) :
    ‖borelOperator A hA a b hbounds φ hφ C hC hφC x‖^2 =
      ∫ t, (φ t)^2 ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [← operator_spectral_integral_one A hA a b hbounds,
    borel_operator_scalar_measure A hA a b hbounds φ hφ C hC hφC]
  rw [finiteDensity_integral _ (fun t => (φ t)^2) _
    ((continuous_pow 2).measurable.comp hφ) (fun t => sq_nonneg (φ t))]
  simp only [mul_one]

/-- The constructed multiplier has its expected original-Hilbert-space bound. -/
theorem borel_operator_norm_le (x : E) :
    ‖borelOperator A hA a b hbounds φ hφ C hC hφC x‖ ≤ C * ‖x‖ := by
  have hs : ‖borelOperator A hA a b hbounds φ hφ C hC hφC x‖^2 ≤ C^2 * ‖x‖^2 := by
    rw [borel_operator_norm_sq]
    calc
      _ ≤ ∫ _t : Icc a b, C^2 ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
        apply integral_mono (borel_square_integrable A hA a b hbounds φ hφ C hφC x) (integrable_const _)
        intro t
        calc
          (φ t)^2 = |φ t|^2 := (sq_abs _).symm
          _ ≤ C^2 := pow_le_pow_left (abs_nonneg _) (hφC t) 2
      _ = C^2 * ‖x‖^2 := by
        calc
          _ = ∫ _t : Icc a b, C^2 * 1 ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by simp
          _ = _ := by rw [integral_mul_left, operator_spectral_integral_one]
  have hn := norm_nonneg (borelOperator A hA a b hbounds φ hφ C hC hφC x)
  have hx := mul_nonneg hC (norm_nonneg x)
  nlinarith only [hs, hn, hx]

/-- Independence of the chosen numerical bound and hence of the positive shift. -/
theorem borel_operator_independent_bound (D : ℝ) (hD : 0 ≤ D) (hφD : ∀ t, |φ t| ≤ D) :
    borelOperator A hA a b hbounds φ hφ C hC hφC =
      borelOperator A hA a b hbounds φ hφ D hD hφD := by
  apply symmetric_operator_eq_of_diagonal _ _
    (borel_operator_symmetric A hA a b hbounds φ hφ C hC hφC)
    (borel_operator_symmetric A hA a b hbounds φ hφ D hD hφD)
  intro x
  rw [borel_operator_self, borel_operator_self]

end BB
