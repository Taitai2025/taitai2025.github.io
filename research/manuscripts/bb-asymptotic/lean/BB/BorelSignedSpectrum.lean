import BB.BorelProjection
import BB.BorelSpectrum

/-!
# Signed Borel functional calculus on the actual spectrum

The domain is the actual real spectrum, and the probability measure itself is
constructed on that spectrum. The exact normalized Borel integral formula is
proved for every bounded real-valued Borel function, with no PVM premise.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace BB
open MeasureTheory Set Filter
open scoped Topology Polynomial ENNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)

/-- The exact normalized scalar integral formula, before changing the domain to the actual spectrum. -/
theorem borel_operator_normalized_form (φ : Icc a b → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (hφC : ∀ t, |φ t| ≤ C) (x : E) (hx : x ≠ 0) :
    ⟪borelOperator A hA a b hbounds φ hφ C hC hφC x, x⟫ / ‖x‖^2 =
      ∫ t, φ t ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
  rw [borel_operator_self, operator_spectral_measure_nonzero A hA a b hbounds x hx,
    integral_smul_measure, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]
  have hn : ‖x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
  field_simp

lemma spectrumIntervalWeight_abs_bound (φ : spectrum ℝ A → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hφC : ∀ t, |φ t| ≤ C) (t : Icc a b) :
    |spectrumIntervalWeight A a b φ 0 t| ≤ C := by
  unfold spectrumIntervalWeight extendSpectrumWeight
  split_ifs with ht
  · exact hφC ⟨t, ht⟩
  · simpa only [abs_zero] using hC

variable (φ : spectrum ℝ A → ℝ) (hφ : Measurable φ) (C : ℝ) (hC : 0 ≤ C)
  (hφC : ∀ t, |φ t| ≤ C)

/-- The bounded signed Borel operator for a function defined only on the actual spectrum. -/
def spectralSignedBorelOperator : E →L[ℝ] E :=
  borelOperator A hA a b hbounds (spectrumIntervalWeight A a b φ 0)
    (spectrumIntervalWeight_measurable A a b φ hφ 0) C hC
    (spectrumIntervalWeight_abs_bound A a b φ C hC hφC)

theorem spectral_signed_borel_operator_symmetric :
    (spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC).toLinearMap.IsSymmetric :=
  borel_operator_symmetric _ _ _ _ _ _ _ _ _ _

theorem spectral_signed_borel_operator_commute :
    Commute (spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC) A :=
  borel_operator_commute _ _ _ _ _ _ _ _ _ _

theorem spectral_signed_borel_operator_norm_le (x : E) :
    ‖spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC x‖ ≤ C*‖x‖ :=
  borel_operator_norm_le _ _ _ _ _ _ _ _ _ _ x

/-- Any bounded measurable interval extension yields the same signed operator. -/
theorem spectral_signed_borel_operator_eq_extension (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
    (D : ℝ) (hD : 0 ≤ D) (hψD : ∀ t, |ψ t| ≤ D)
    (hmatch : ∀ (t : Icc a b) (ht : (t : ℝ) ∈ spectrum ℝ A), ψ t = φ ⟨t, ht⟩) :
    borelOperator A hA a b hbounds ψ hψ D hD hψD =
      spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC := by
  apply symmetric_operator_eq_of_diagonal _ _
    (borel_operator_symmetric A hA a b hbounds ψ hψ D hD hψD)
    (spectral_signed_borel_operator_symmetric A hA a b hbounds φ hφ C hC hφC)
  intro x
  rw [borel_operator_self, spectralSignedBorelOperator, borel_operator_self]
  apply integral_congr_ae
  filter_upwards [operator_spectral_measure_ae_mem_spectrum A hA a b hbounds x] with t ht
  rw [hmatch t ht]
  exact (extendSpectrumWeight_on_spectrum A φ 0 ⟨t, ht⟩).symm

/-- The signed construction agrees with the original positive Borel construction. -/
theorem spectral_signed_borel_operator_eq_positive (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (hφbounds : ∀ t, l ≤ φ t ∧ φ t ≤ u) :
    spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC =
      spectralBorelOperator A hA a b hbounds φ hφ l u hl hlu hφbounds := by
  apply symmetric_operator_eq_of_diagonal _ _
    (spectral_signed_borel_operator_symmetric A hA a b hbounds φ hφ C hC hφC)
    (spectral_borel_operator_symmetric A hA a b hbounds φ hφ l u hl hlu hφbounds)
  intro x
  rw [spectralSignedBorelOperator, borel_operator_self, spectralBorelOperator, borel_weight_operator_self]
  apply integral_congr_ae
  filter_upwards [operator_spectral_measure_ae_mem_spectrum A hA a b hbounds x] with t ht
  exact (extendSpectrumWeight_on_spectrum A φ 0 ⟨t, ht⟩).trans
    (extendSpectrumWeight_on_spectrum A φ l ⟨t, ht⟩).symm

/-- Agreement with genuine polynomial evaluation, without any positivity assumption on the polynomial. -/
theorem spectral_signed_borel_operator_polynomial (p : ℝ[X])
    (hp : ∀ t : spectrum ℝ A, φ t = p.eval (t : ℝ)) :
    spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC = Polynomial.aeval A p := by
  apply symmetric_operator_eq_of_diagonal _ _
    (spectral_signed_borel_operator_symmetric A hA a b hbounds φ hφ C hC hφC)
    (operator_polynomial_symmetric A hA p)
  intro x
  rw [spectralSignedBorelOperator, borel_operator_self]
  calc
    _ = ∫ t, p.eval (t : ℝ) ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
      apply integral_congr_ae
      filter_upwards [operator_spectral_measure_ae_mem_spectrum A hA a b hbounds x] with t ht
      exact (extendSpectrumWeight_on_spectrum A φ 0 ⟨t, ht⟩).trans (hp ⟨t, ht⟩)
    _ = ⟪x, polynomialVector A x p⟫ := operator_spectral_polynomial_integral A hA a b hbounds x p
    _ = _ := real_inner_comm _ _

/-- A measurable retraction onto the actual spectrum, used only off a null set. -/
def spectrumRetraction (r : spectrum ℝ A) : Icc a b → spectrum ℝ A :=
  fun t => if ht : (t : ℝ) ∈ spectrum ℝ A then ⟨t, ht⟩ else r

lemma spectrumRetraction_measurable (r : spectrum ℝ A) :
    Measurable (spectrumRetraction A a b r) := by
  let f : {t : Icc a b | (t : ℝ) ∈ spectrum ℝ A} → spectrum ℝ A :=
    fun t => ⟨(t : Icc a b), t.2⟩
  have hf : Measurable f :=
    (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  exact hf.dite measurable_const ((spectrum.isClosed A).measurableSet.preimage measurable_subtype_coe)

lemma spectrum_nonempty_of_nonzero (x : E) (hx : x ≠ 0) : Nonempty (spectrum ℝ A) := by
  obtain ⟨t, ht⟩ := (operator_spectral_probability_ae_mem_spectrum A hA a b hbounds x hx).exists
  exact ⟨⟨t, ht⟩⟩

/-- Actual probability measure whose underlying space is the actual spectrum. -/
def operatorIntrinsicSpectralProbability (x : E) (hx : x ≠ 0) : ProbabilityMeasure (spectrum ℝ A) :=
  (operatorSpectralProbability A hA a b hbounds x hx).map
    (spectrumRetraction_measurable A a b (Classical.choice
      (spectrum_nonempty_of_nonzero A hA a b hbounds x hx))).aemeasurable

/-- Exact normalized Borel functional calculus on the actual spectrum, literally the source formula. -/
theorem spectral_signed_borel_normalized_form (x : E) (hx : x ≠ 0) :
    ⟪spectralSignedBorelOperator A hA a b hbounds φ hφ C hC hφC x, x⟫ / ‖x‖^2 =
      ∫ t, φ t ∂(operatorIntrinsicSpectralProbability A hA a b hbounds x hx : Measure (spectrum ℝ A)) := by
  rw [spectralSignedBorelOperator, borel_operator_normalized_form]
  symm
  change (∫ t, φ t ∂Measure.map
    (spectrumRetraction A a b (Classical.choice (spectrum_nonempty_of_nonzero A hA a b hbounds x hx)))
    (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) = _
  rw [integral_map (spectrumRetraction_measurable A a b _).aemeasurable hφ.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [operator_spectral_probability_ae_mem_spectrum A hA a b hbounds x hx] with t ht
  simp only [spectrumRetraction, dif_pos ht, spectrumIntervalWeight, extendSpectrumWeight, dif_pos ht]

end BB
