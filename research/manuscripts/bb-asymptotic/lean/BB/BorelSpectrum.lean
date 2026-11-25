import BB.BorelPolynomial
import BB.OperatorSpectrumSupport
import Mathlib.Analysis.NormedSpace.Spectrum

/-!
# Borel weights defined on the actual spectrum

The interval construction is made intrinsic to the actual spectrum. A Borel
weight on the closed real spectrum is extended by a positive constant, and the
proved scalar support theorem shows that the resulting operator is independent
of all values away from the spectrum. Polynomial agreement is also proved.
-/

noncomputable section
attribute [local instance] Classical.propDecidable
namespace BB
open MeasureTheory Set
open scoped Topology Polynomial
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Extend a weight from the actual real spectrum by a specified constant. -/
def extendSpectrumWeight (A : E →L[ℝ] E) (Ψ : spectrum ℝ A → ℝ) (c : ℝ) : ℝ → ℝ :=
  fun t => if ht : t ∈ spectrum ℝ A then Ψ ⟨t, ht⟩ else c

lemma extendSpectrumWeight_measurable (A : E →L[ℝ] E) (Ψ : spectrum ℝ A → ℝ)
    (hΨ : Measurable Ψ) (c : ℝ) : Measurable (extendSpectrumWeight A Ψ c) := by
  exact hΨ.dite measurable_const (spectrum.isClosed A).measurableSet

lemma extendSpectrumWeight_on_spectrum (A : E →L[ℝ] E) (Ψ : spectrum ℝ A → ℝ)
    (c : ℝ) (t : spectrum ℝ A) : extendSpectrumWeight A Ψ c (t : ℝ) = Ψ t := by
  simp only [extendSpectrumWeight, dif_pos t.2]

lemma extendSpectrumWeight_bounds (A : E →L[ℝ] E) (Ψ : spectrum ℝ A → ℝ)
    (l u : ℝ) (hlu : l ≤ u) (hΨbounds : ∀ t, l ≤ Ψ t ∧ Ψ t ≤ u) (t : ℝ) :
    l ≤ extendSpectrumWeight A Ψ l t ∧ extendSpectrumWeight A Ψ l t ≤ u := by
  unfold extendSpectrumWeight
  split_ifs with ht
  · exact hΨbounds ⟨t, ht⟩
  · exact ⟨le_rfl, hlu⟩

/-- The interval test uses only restriction of the Borel extension. -/
def spectrumIntervalWeight (A : E →L[ℝ] E) (a b : ℝ) (Ψ : spectrum ℝ A → ℝ) (c : ℝ) :
    Icc a b → ℝ := fun t => extendSpectrumWeight A Ψ c (t : ℝ)

lemma spectrumIntervalWeight_measurable (A : E →L[ℝ] E) (a b : ℝ)
    (Ψ : spectrum ℝ A → ℝ) (hΨ : Measurable Ψ) (c : ℝ) :
    Measurable (spectrumIntervalWeight A a b Ψ c) :=
  (extendSpectrumWeight_measurable A Ψ hΨ c).comp measurable_subtype_coe

variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)

/-- Values away from the actual spectrum cannot change the constructed operator. -/
theorem borel_weight_operator_congr_spectrum
    (ψ χ : Icc a b → ℝ) (hψ : Measurable ψ) (hχ : Measurable χ)
    (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
    (hψb : ∀ t, l ≤ ψ t ∧ ψ t ≤ u) (hχb : ∀ t, l ≤ χ t ∧ χ t ≤ u)
    (heq : ∀ t : Icc a b, (t : ℝ) ∈ spectrum ℝ A → ψ t = χ t) :
    borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψb =
      borelWeightOperator A hA a b hbounds χ hχ l u hl hlu hχb := by
  apply symmetric_operator_eq_of_diagonal _ _
    (borel_weight_operator_symmetric A hA a b hbounds ψ hψ l u hl hlu hψb)
    (borel_weight_operator_symmetric A hA a b hbounds χ hχ l u hl hlu hχb)
  intro x
  rw [borel_weight_operator_self, borel_weight_operator_self]
  apply integral_congr_ae
  filter_upwards [operator_spectral_measure_ae_mem_spectrum A hA a b hbounds x] with t ht
  exact heq t ht

variable (Ψ : spectrum ℝ A → ℝ) (hΨ : Measurable Ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) (hΨbounds : ∀ t, l ≤ Ψ t ∧ Ψ t ≤ u)

/-- The actual source-domain operator Ψ(A), with no interval extension premise. -/
def spectralBorelOperator : E →L[ℝ] E :=
  borelWeightOperator A hA a b hbounds (spectrumIntervalWeight A a b Ψ l)
    (spectrumIntervalWeight_measurable A a b Ψ hΨ l) l u hl hlu
    (fun t => extendSpectrumWeight_bounds A Ψ l u hlu hΨbounds (t : ℝ))

theorem spectral_borel_operator_symmetric :
    (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap.IsSymmetric :=
  borel_weight_operator_symmetric _ _ _ _ _ _ _ _ _ _ _ _

theorem spectral_borel_operator_bounds (x : E) :
    l * ‖x‖^2 ≤ ⟪x, spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x⟫ ∧
      ⟪x, spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds x⟫ ≤ u * ‖x‖^2 :=
  borel_weight_operator_bounds _ _ _ _ _ _ _ _ _ _ _ _ x

theorem spectral_borel_operator_commute :
    Commute (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds) A :=
  borel_weight_operator_commute _ _ _ _ _ _ _ _ _ _ _ _

/-- Any bounded Borel extension gives precisely the same source-domain operator. -/
theorem spectral_borel_operator_eq_extension (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
    (hψb : ∀ t, l ≤ ψ t ∧ ψ t ≤ u)
    (hmatch : ∀ (t : Icc a b) (ht : (t : ℝ) ∈ spectrum ℝ A), ψ t = Ψ ⟨t, ht⟩) :
    borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψb =
      spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds := by
  apply borel_weight_operator_congr_spectrum A hA a b hbounds ψ _ hψ _ l u hl hlu hψb _
  intro t ht
  rw [hmatch t ht]
  exact (extendSpectrumWeight_on_spectrum A Ψ l ⟨t, ht⟩).symm

/-- The intrinsic Borel construction agrees with actual polynomial evaluation
whenever the spectral weight is a positive bounded real polynomial. -/
theorem spectral_borel_operator_polynomial (p : ℝ[X])
    (hp : ∀ t : spectrum ℝ A, Ψ t = p.eval (t : ℝ)) :
    spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds = Polynomial.aeval A p := by
  apply symmetric_operator_eq_of_diagonal _ _
    (spectral_borel_operator_symmetric A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds)
    (operator_polynomial_symmetric A hA p)
  intro x
  rw [spectralBorelOperator, borel_weight_operator_self]
  calc
    _ = ∫ t, p.eval (t : ℝ)
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
      apply integral_congr_ae
      filter_upwards [operator_spectral_measure_ae_mem_spectrum A hA a b hbounds x] with t ht
      change extendSpectrumWeight A Ψ l (t : ℝ) = p.eval (t : ℝ)
      rw [extendSpectrumWeight_on_spectrum A Ψ l ⟨t, ht⟩, hp ⟨t, ht⟩]
    _ = ⟪x, polynomialVector A x p⟫ := operator_spectral_polynomial_integral A hA a b hbounds x p
    _ = ⟪(Polynomial.aeval A p) x, x⟫ := real_inner_comm _ _

end BB
