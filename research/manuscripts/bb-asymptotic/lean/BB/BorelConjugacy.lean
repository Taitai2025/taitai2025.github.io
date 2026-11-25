import BB.BorelPolynomial
import BB.HilbertConjugacy

/-!
# Exact scalar spectral measures under a Borel square-root conjugacy

The constructed Borel operator and a genuine commuting square root determine
all transformed scalar moments. Moment uniqueness then proves the actual
withDensity formula, normalization, and equality of spectral supports.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

section MeasureFacts
variable {K : Type*} [MeasurableSpace K]

theorem normalize_smul_probability (ν : ProbabilityMeasure K) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞) :
    ((c • (ν : Measure K)) univ)⁻¹ • (c • (ν : Measure K)) = (ν : Measure K) := by
  rw [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one, smul_smul,
    ENNReal.inv_mul_cancel hc0 hcTop, one_smul]

theorem normalizedReweight_smul (μ : Measure K) (q : K → ℝ≥0∞) (c : ℝ≥0∞)
    (hc0 : c ≠ 0) (hcTop : c ≠ ∞) :
    normalizedReweight (c • μ) q = normalizedReweight μ q := by
  unfold normalizedReweight
  rw [lintegral_smul_measure, withDensity_smul_measure, smul_smul]
  congr 1
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hcTop)]
  calc
    (c⁻¹ * (∫⁻ x, q x ∂μ)⁻¹) * c = (∫⁻ x, q x ∂μ)⁻¹ * (c⁻¹ * c) := by ring
    _ = (∫⁻ x, q x ∂μ)⁻¹ := by rw [ENNReal.inv_mul_cancel hc0 hcTop, mul_one]

theorem measureSupport_smul_eq [TopologicalSpace K] (μ : Measure K) (c : ℝ≥0∞) (hc : c ≠ 0) :
    measureSupport (c • μ) = measureSupport μ := by
  ext x
  simp only [measureSupport, mem_setOf_eq, Measure.smul_apply, smul_eq_mul,
    ne_eq, mul_eq_zero, hc, false_or]

theorem finiteDensity_support_eq [TopologicalSpace K] (μ : FiniteMeasure K) (q : K → ℝ)
    (hqi : Integrable q (μ : Measure K)) (hqm : Measurable q) (hqpos : ∀ x, 0 < q x) :
    measureSupport (finiteDensity μ q hqi : Measure K) = measureSupport (μ : Measure K) := by
  apply Subset.antisymm
  · exact measureSupport_subset_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)
  · exact measureSupport_subset_of_absolutelyContinuous
      (withDensity_absolutelyContinuous' hqm.ennreal_ofReal.aemeasurable
        (Filter.eventually_of_forall (fun x => (ENNReal.ofReal_pos.mpr (hqpos x)).ne')))

end MeasureFacts

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)
  (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
  (hψbounds : ∀ t, l ≤ ψ t ∧ ψ t ≤ u)

lemma commute_iterate_apply (S : E →L[ℝ] E) (hcomm : ∀ x, S (A x) = A (S x)) (x : E) (k : ℕ) :
    S ((A : E → E)^[k] x) = (A : E → E)^[k] (S x) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]

/-- The measure identity is unconditional at zero and at finite-termination vectors. -/
theorem borel_square_root_scalar_measure (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds = S.comp S)
    (hcomm : ∀ x, S (A x) = A (S x)) (x : E) :
    operatorSpectralMeasure A hA a b hbounds (S x) =
      finiteDensity (operatorSpectralMeasure A hA a b hbounds x) ψ
        (borel_weight_integrable A hA a b hbounds ψ hψ l u hl hψbounds x) := by
  apply finite_measure_eq_of_moments a b
  intro k
  rw [operator_spectral_measure_moment,
    finiteDensity_integral _ ψ _ hψ (fun t => hl.le.trans (hψbounds t).1)]
  calc
    ⟪S x, (A : E → E)^[k] (S x)⟫ = ⟪S x, S ((A : E → E)^[k] x)⟫ := by
      rw [commute_iterate_apply A S hcomm]
    _ = ⟪S (S x), (A : E → E)^[k] x⟫ := (hS _ _).symm
    _ = ⟪borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x,
        (A : E → E)^[k] x⟫ := by rw [hsquare]; rfl
    _ = ∫ t, (t : ℝ)^k * ψ t
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) :=
      borel_weight_operator_power_inner A hA a b hbounds ψ hψ l u hl hlu hψbounds x k
    _ = _ := integral_congr_ae (Filter.eventually_of_forall (fun _ => mul_comm _ _))

theorem borel_square_root_ne_zero (S : E →L[ℝ] E)
    (hsquare : borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds = S.comp S)
    (x : E) (hx : x ≠ 0) : S x ≠ 0 := by
  intro hSx
  have hb := (borel_weight_operator_bounds A hA a b hbounds ψ hψ l u hl hlu hψbounds x).1
  rw [hsquare] at hb
  change l * ‖x‖^2 ≤ ⟪x, S (S x)⟫ at hb
  rw [hSx, map_zero, inner_zero_right] at hb
  exact (not_le_of_gt (mul_pos hl (sq_pos_of_pos (norm_pos_iff.mpr hx)))) hb

/-- Normalizing the unnormalized measure recovers the original spectral probability. -/
theorem operator_spectral_probability_normalize (x : E) (hx : x ≠ 0) :
    (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) =
      ((operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) univ)⁻¹ •
        (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [operator_spectral_measure_nonzero A hA a b hbounds x hx]
  symm
  exact normalize_smul_probability _ _
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hx))).ne' ENNReal.ofReal_ne_top

/-- This is the exact normalized spectral-density formula used in the paper. -/
theorem borel_square_root_spectral_probability (S : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric)
    (hsquare : borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds = S.comp S)
    (hcomm : ∀ x, S (A x) = A (S x)) (x : E) (hx : x ≠ 0) (hSx : S x ≠ 0) :
    (operatorSpectralProbability A hA a b hbounds (S x) hSx : Measure (Icc a b)) =
      normalizedReweight (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))
        (fun t => ENNReal.ofReal (ψ t)) := by
  rw [operator_spectral_probability_normalize A hA a b hbounds (S x) hSx,
    borel_square_root_scalar_measure A hA a b hbounds ψ hψ l u hl hlu hψbounds S hS hsquare hcomm x]
  change (((operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)).withDensity
      (fun t => ENNReal.ofReal (ψ t))) univ)⁻¹ •
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)).withDensity
        (fun t => ENNReal.ofReal (ψ t)) = _
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  change normalizedReweight (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))
      (fun t => ENNReal.ofReal (ψ t)) = _
  rw [operator_spectral_measure_nonzero A hA a b hbounds x hx]
  exact normalizedReweight_smul _ _ _
    (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (norm_pos_iff.mpr hx))).ne' ENNReal.ofReal_ne_top

/-- Uniformly positive Borel weights preserve the actual scalar spectral support. -/
theorem borel_square_root_support (S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds = S.comp S)
    (hcomm : ∀ x, S (A x) = A (S x)) (x : E) (hx : x ≠ 0) (hSx : S x ≠ 0) :
    measureSupport (operatorSpectralProbability A hA a b hbounds (S x) hSx : Measure (Icc a b)) =
      measureSupport (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
  have hmass : (∫⁻ t, ENNReal.ofReal (ψ t)
      ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) ≠ ∞ := by
    have hi : Integrable ψ (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
      apply (integrable_const u).mono' hψ.aestronglyMeasurable
      apply Filter.eventually_of_forall
      intro t
      rw [Real.norm_eq_abs, abs_of_nonneg (hl.le.trans (hψbounds t).1)]
      exact (hψbounds t).2
    rw [← ofReal_integral_eq_lintegral_ofReal hi
      (Filter.eventually_of_forall (fun t => hl.le.trans (hψbounds t).1))]
    exact ENNReal.ofReal_ne_top
  rw [borel_square_root_spectral_probability A hA a b hbounds ψ hψ l u hl hlu hψbounds S hS hsquare hcomm]
  exact normalizedReweight_support_eq _ _ hψ.ennreal_ofReal.aemeasurable
    (Filter.eventually_of_forall (fun t => (ENNReal.ofReal_pos.mpr (hl.trans_le (hψbounds t).1)).ne')) hmass

end BB
