import BB.BorelFunctionalCalculus
import BB.OperatorPolynomial

/-!
# Polynomial density identities for the constructed Borel operator

These identities connect actual scalar spectral measures with multiplication by
polynomials in the actual bounded operator. They subsequently identify all
weighted moments, including the intrinsic support after conjugacy.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology Polynomial NNReal ENNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

section Density
variable {K : Type*} [MeasurableSpace K]

/-- An integrable real density gives a genuine finite measure. -/
def finiteDensity (μ : FiniteMeasure K) (q : K → ℝ)
    (hq : Integrable q (μ : Measure K)) : FiniteMeasure K :=
  ⟨(μ : Measure K).withDensity (fun x => ENNReal.ofReal (q x)),
    isFiniteMeasure_withDensity_ofReal hq.hasFiniteIntegral⟩

/-- The density integration formula for arbitrary real tests. -/
theorem finiteDensity_integral (μ : FiniteMeasure K) (q : K → ℝ)
    (hqi : Integrable q (μ : Measure K)) (hqm : Measurable q) (hq0 : ∀ x, 0 ≤ q x)
    (f : K → ℝ) :
    (∫ x, f x ∂(finiteDensity μ q hqi : Measure K)) = ∫ x, q x * f x ∂(μ : Measure K) := by
  let qNN : K → ℝ≥0 := fun x => ⟨q x, hq0 x⟩
  have hden : (fun x => ENNReal.ofReal (q x)) = (fun x => (qNN x : ℝ≥0∞)) := by
    funext x
    exact ENNReal.ofReal_eq_coe_nnreal (hq0 x)
  have hqNN : Measurable qNN := measurable_coe_nnreal_real_iff.mp hqm
  change (∫ x, f x ∂(μ : Measure K).withDensity (fun x => ENNReal.ofReal (q x))) = _
  rw [hden, integral_withDensity_eq_integral_smul hqNN]
  rfl

end Density

lemma continuous_mul_integrable {K : Type*} [TopologicalSpace K] [CompactSpace K]
    [MeasurableSpace K] [OpensMeasurableSpace K]
    (μ : FiniteMeasure K) (f : C(K, ℝ)) (g : K → ℝ) (hg : Integrable g (μ : Measure K)) :
    Integrable (fun x => f x * g x) (μ : Measure K) :=
  hg.bdd_mul f.continuous.measurable.aestronglyMeasurable ⟨‖f‖, f.norm_coe_le_norm⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma polynomial_vector_iterate (A : E →L[ℝ] E) (x : E) (p : ℝ[X]) (k : ℕ) :
    (A : E → E)^[k] (polynomialVector A x p) = polynomialVector A x (Polynomial.X^k * p) := by
  induction k with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_mul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← polynomial_vector_X_mul]
    congr 1
    rw [pow_succ']
    ring

variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)

/-- All polynomial integrals of the unnormalized scalar spectral measure. -/
theorem operator_spectral_polynomial_integral (x : E) (p : ℝ[X]) :
    (∫ t, p.eval (t : ℝ)
      ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) =
      ⟪x, polynomialVector A x p⟫ := by
  by_cases hx : x = 0
  · subst x
    simp
  · change (∫ t, p.toContinuousMapOn (Icc a b) t ∂(_ : Measure (Icc a b))) = _
    rw [operator_spectral_measure_integral A hA a b hbounds x hx,
      operator_moment_state_polynomial]
    have hn : ‖x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
    field_simp

/-- Exact unnormalized spectral reweighting by the square of any real polynomial. -/
theorem operator_spectral_polynomial_density (x : E) (p : ℝ[X]) :
    operatorSpectralMeasure A hA a b hbounds (polynomialVector A x p) =
      finiteDensity (operatorSpectralMeasure A hA a b hbounds x)
        (fun t : Icc a b => (p.eval (t : ℝ))^2)
        (continuous_integrable_finite _ ((p.toContinuousMapOn (Icc a b))^2)) := by
  apply finite_measure_eq_of_moments a b
  intro k
  rw [operator_spectral_measure_moment, finiteDensity_integral]
  · rw [polynomial_vector_iterate, polynomial_vector_inner A hA]
    rw [← operator_spectral_polynomial_integral A hA a b hbounds x (p * (Polynomial.X^k * p))]
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
    ring
  · exact ((p.toContinuousMapOn (Icc a b)).continuous.pow 2).measurable
  · intro t
    exact sq_nonneg _

/-- Any Borel test can be evaluated after applying a polynomial to the vector. -/
theorem operator_spectral_polynomial_test (x : E) (p : ℝ[X]) (ψ : Icc a b → ℝ) :
    (∫ t, ψ t ∂(operatorSpectralMeasure A hA a b hbounds (polynomialVector A x p) : Measure (Icc a b))) =
      ∫ t, (p.eval (t : ℝ))^2 * ψ t
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [operator_spectral_polynomial_density]
  exact finiteDensity_integral _ _ _ ((p.toContinuousMapOn (Icc a b)).continuous.pow 2).measurable
      (fun t => sq_nonneg _) ψ

/-- Real symmetric operator polarization, without any spectral assumption. -/
theorem symmetric_operator_polarization (W : E →L[ℝ] E) (hW : W.toLinearMap.IsSymmetric) (x y : E) :
    ⟪W x, y⟫ = (⟪W (x + y), x + y⟫ - ⟪W (x - y), x - y⟫) / 4 := by
  have hxy : ⟪W y, x⟫ = ⟪W x, y⟫ := by
    calc
      _ = ⟪y, W x⟫ := hW _ _
      _ = _ := real_inner_comm (W x) y
  simp only [map_add, map_sub, inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [hxy]
  ring


section WeightedMoments
variable [CompleteSpace E]
variable (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
  (hψbounds : ∀ t, l ≤ ψ t ∧ ψ t ≤ u)

/-- The mixed polynomial integral identity identifies the Borel operator on the
entire polynomial cyclic space, not only its diagonal value. -/
theorem borel_weight_operator_polynomial_inner (x : E) (p : ℝ[X]) :
    ⟪borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x,
      polynomialVector A x p⟫ =
      ∫ t, p.eval (t : ℝ) * ψ t
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [symmetric_operator_polarization _
    (borel_weight_operator_symmetric A hA a b hbounds ψ hψ l u hl hlu hψbounds),
    borel_weight_operator_self, borel_weight_operator_self]
  have hplus : x + polynomialVector A x p = polynomialVector A x (1 + p) := by
    simp only [polynomialVector, map_add, map_one, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.one_apply]
  have hminus : x - polynomialVector A x p = polynomialVector A x (1 - p) := by
    simp only [polynomialVector, map_sub, map_one, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply]
  rw [hplus, hminus, operator_spectral_polynomial_test, operator_spectral_polynomial_test]
  have hψi := borel_weight_integrable A hA a b hbounds ψ hψ l u hl hψbounds x
  have hp : Integrable (fun t : Icc a b => ((1 + p).eval (t : ℝ))^2 * ψ t)
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
    by simpa only [ContinuousMap.pow_apply] using
      continuous_mul_integrable _ (((1+p).toContinuousMapOn (Icc a b))^2) ψ hψi
  have hm : Integrable (fun t : Icc a b => ((1 - p).eval (t : ℝ))^2 * ψ t)
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
    by simpa only [ContinuousMap.pow_apply] using
      continuous_mul_integrable _ (((1-p).toContinuousMapOn (Icc a b))^2) ψ hψi
  rw [← integral_sub hp hm, ← integral_div]
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_one]
  ring

/-- All mixed weighted moments are actual Borel integrals. -/
theorem borel_weight_operator_power_inner (x : E) (k : ℕ) :
    ⟪borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x,
      (A : E → E)^[k] x⟫ =
      ∫ t, (t : ℝ)^k * ψ t
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  simpa only [polynomialVector, map_pow, Polynomial.aeval_X, ContinuousLinearMap.coe_pow,
    Polynomial.eval_pow, Polynomial.eval_X] using
    borel_weight_operator_polynomial_inner A hA a b hbounds ψ hψ l u hl hlu hψbounds x (Polynomial.X^k)

end WeightedMoments

end BB
