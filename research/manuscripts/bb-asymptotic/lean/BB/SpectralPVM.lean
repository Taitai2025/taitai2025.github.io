import BB.SpectralPVMCore
import BB.BorelProjection
import BB.BorelSignedSpectrum
import BB.BalancedRealization
import Mathlib.Analysis.NormedSpace.Spectrum

/-!
# The actual spectral projection-valued measure of a bounded symmetric operator

The projection family is constructed from the bounded Borel indicator calculus,
then the scalar-measure identities give a genuine strongly countably additive
projection-valued measure. It is pushed to real Borel sets and its scalar masses
are identified with the already constructed spectral probabilities. Thus the
source's displayed projection formula is an identity of actual objects.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology BigOperators Polynomial
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)

/-- The actual spectral PVM on the bounding interval. -/
def intervalSpectralPVM : ProjectionValuedMeasure (Icc a b) E :=
  projectionValuedMeasureOfScalar
    (spectralProjection A hA a b hbounds)
    (operatorSpectralMeasure A hA a b hbounds)
    (spectral_projection_symmetric A hA a b hbounds)
    (spectral_projection_self A hA a b hbounds)
    (spectral_projection_norm_sq A hA a b hbounds)
    (operator_spectral_measure_univ A hA a b hbounds)
    (spectral_projection_measure A hA a b hbounds)

/-- The source's real Borel spectral PVM, with all PVM axioms proved. -/
def operatorSpectralPVM : ProjectionValuedMeasure ℝ E :=
  (intervalSpectralPVM A hA a b hbounds).mapMeasurable Subtype.val measurable_subtype_coe

@[simp] theorem operator_spectral_pvm_apply (B : Set ℝ) (hB : MeasurableSet B) :
    (operatorSpectralPVM A hA a b hbounds).map B hB =
      spectralProjection A hA a b hbounds (Subtype.val ⁻¹' B) (hB.preimage measurable_subtype_coe) := rfl

theorem operator_spectral_pvm_singleton (r : Icc a b) :
    (operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)} (measurableSet_singleton _) =
      spectralProjection A hA a b hbounds {r} (measurableSet_singleton r) := by
  rw [operator_spectral_pvm_apply]
  have heq : (Subtype.val : Icc a b → ℝ) ⁻¹' {(r : ℝ)} = {r} := by
    ext t
    simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
  congr 1

/-- Strong countable additivity for the actual operator spectral projections. -/
theorem operator_spectral_pvm_countably_additive (B : ℕ → Set ℝ)
    (hB : ∀ n, MeasurableSet (B n))
    (hdis : Pairwise (fun n m => Disjoint (B n) (B m))) (x : E) :
    Tendsto (fun n => ∑ i ∈ Finset.range n,
      (operatorSpectralPVM A hA a b hbounds).map (B i) (hB i) x) atTop
      (𝓝 ((operatorSpectralPVM A hA a b hbounds).map (⋃ i, B i) (MeasurableSet.iUnion hB) x)) :=
  (operatorSpectralPVM A hA a b hbounds).countably_additive B hB hdis x

theorem operator_spectral_pvm_norm_sq (B : Set ℝ) (hB : MeasurableSet B) (x : E) :
    ‖(operatorSpectralPVM A hA a b hbounds).map B hB x‖^2 =
      ((operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) (Subtype.val ⁻¹' B)).toReal :=
  spectral_projection_norm_sq A hA a b hbounds (Subtype.val ⁻¹' B) (hB.preimage measurable_subtype_coe) x

theorem operator_spectral_probability_projection (B : Set (Icc a b))
    (hB : MeasurableSet B) (x : E) (hx : x ≠ 0) :
    ((operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) B).toReal =
      ‖spectralProjection A hA a b hbounds B hB x‖^2/‖x‖^2 := by
  have h := spectral_projection_norm_sq A hA a b hbounds B hB x
  rw [operator_spectral_measure_nonzero A hA a b hbounds x hx, Measure.smul_apply,
    smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _)] at h
  rw [h]
  exact (mul_div_cancel_left₀ _ (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne').symm

/-- The normalized real scalar spectral probability, explicitly defined by
pushforward of the actual moment probability. -/
def operatorRealSpectralProbability (x : E) (hx : x ≠ 0) : ProbabilityMeasure ℝ :=
  (operatorSpectralProbability A hA a b hbounds x hx).map
    measurable_subtype_coe.aemeasurable

/-- Literal formula ν_x(B) = ‖E_A(B)x‖²/‖x‖² on every real Borel set. -/
theorem operator_real_spectral_probability_projection (B : Set ℝ) (hB : MeasurableSet B)
    (x : E) (hx : x ≠ 0) :
    ((operatorRealSpectralProbability A hA a b hbounds x hx : Measure ℝ) B).toReal =
      ‖(operatorSpectralPVM A hA a b hbounds).map B hB x‖^2/‖x‖^2 := by
  change (Measure.map Subtype.val
    (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) B).toReal = _
  rw [Measure.map_apply measurable_subtype_coe hB]
  exact operator_spectral_probability_projection A hA a b hbounds (Subtype.val ⁻¹' B) (hB.preimage measurable_subtype_coe) x hx

/-- Every spectral projection outside the actual spectrum is zero. -/
theorem operator_spectral_pvm_outside_spectrum (B : Set ℝ) (hB : MeasurableSet B)
    (hdis : Disjoint B (spectrum ℝ A)) :
    (operatorSpectralPVM A hA a b hbounds).map B hB = 0 := by
  ext x
  have hzero : (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))
      (Subtype.val ⁻¹' B) = 0 := by
    have hnot : ∀ᵐ t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)),
        t ∉ Subtype.val ⁻¹' B := by
      filter_upwards [operator_spectral_measure_ae_mem_spectrum A hA a b hbounds x] with t ht
      intro hmem
      exact (disjoint_left.mp hdis) hmem ht
    simpa only [not_not] using ae_iff.mp hnot
  have hn := operator_spectral_pvm_norm_sq A hA a b hbounds B hB x
  rw [hzero, ENNReal.zero_toReal] at hn
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

/-- The real spectral PVM gives identity to the actual spectrum. -/
theorem operator_spectral_pvm_spectrum :
    (operatorSpectralPVM A hA a b hbounds).map (spectrum ℝ A)
      (spectrum.isClosed A).measurableSet = ContinuousLinearMap.id ℝ E := by
  let P := operatorSpectralPVM A hA a b hbounds
  have hu := P.disjoint_union (spectrum ℝ A) (spectrum ℝ A)ᶜ
    (spectrum.isClosed A).measurableSet (spectrum.isClosed A).measurableSet.compl disjoint_compl_right
  have hz := operator_spectral_pvm_outside_spectrum A hA a b hbounds
    (spectrum ℝ A)ᶜ (spectrum.isClosed A).measurableSet.compl disjoint_compl_left
  change P.map (spectrum ℝ A)ᶜ (spectrum.isClosed A).measurableSet.compl = 0 at hz
  simpa only [union_compl_self, P.univ, hz, add_zero] using hu.symm

/-- The intrinsic spectral probability and the real spectral probability are
the same measure after the canonical inclusion of the spectrum. -/
theorem operator_intrinsic_spectral_probability_map (x : E) (hx : x ≠ 0) :
    Measure.map (Subtype.val : spectrum ℝ A → ℝ)
      (operatorIntrinsicSpectralProbability A hA a b hbounds x hx : Measure (spectrum ℝ A)) =
      (operatorRealSpectralProbability A hA a b hbounds x hx : Measure ℝ) := by
  change Measure.map Subtype.val (Measure.map
    (spectrumRetraction A a b (Classical.choice (spectrum_nonempty_of_nonzero A hA a b hbounds x hx)))
    (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) =
    Measure.map Subtype.val (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))
  rw [Measure.map_map measurable_subtype_coe (spectrumRetraction_measurable A a b _)]
  apply Measure.map_congr
  filter_upwards [operator_spectral_probability_ae_mem_spectrum A hA a b hbounds x hx] with t ht
  simp only [Function.comp_apply, spectrumRetraction, dif_pos ht]

/-- The literal projection formula on a Borel subset of the actual spectrum. -/
theorem operator_intrinsic_spectral_probability_projection
    (B : Set (spectrum ℝ A)) (hB : MeasurableSet B) (x : E) (hx : x ≠ 0) :
    ((operatorIntrinsicSpectralProbability A hA a b hbounds x hx : Measure (spectrum ℝ A)) B).toReal =
      ‖(operatorSpectralPVM A hA a b hbounds).map (Subtype.val '' B)
        ((MeasurableEmbedding.subtype_coe (spectrum.isClosed A).measurableSet).measurableSet_image.mpr hB) x‖^2/‖x‖^2 := by
  have himage : MeasurableSet (Subtype.val '' B : Set ℝ) :=
    (MeasurableEmbedding.subtype_coe (spectrum.isClosed A).measurableSet).measurableSet_image.mpr hB
  have h := operator_real_spectral_probability_projection A hA a b hbounds (Subtype.val '' B) himage x hx
  rw [← operator_intrinsic_spectral_probability_map A hA a b hbounds x hx,
    Measure.map_apply measurable_subtype_coe himage, preimage_image_eq _ Subtype.val_injective] at h
  exact h

/-- Integrating the coordinate function against this spectral measure gives
the original operator, not merely an operator with matching bounds. -/
theorem operator_spectral_coordinate_integral :
    borelOperator A hA a b hbounds (fun t : Icc a b => (t : ℝ)) measurable_subtype_coe
      (max |a| |b|) ((abs_nonneg a).trans (le_max_left _ _))
      (fun t => abs_le_max_abs_abs t.2.1 t.2.2) = A := by
  apply symmetric_operator_eq_of_diagonal _ _
    (borel_operator_symmetric _ _ _ _ _ _ _ _ _ _) hA
  intro x
  rw [borel_operator_self]
  calc
    _ = ⟪x,A x⟫ := by
      simpa only [pow_one, Function.iterate_one] using
        operator_spectral_measure_moment A hA a b hbounds x 1
    _ = ⟪A x,x⟫ := real_inner_comm _ _

/-- Norm-square spectral integration for every actual polynomial, including
the zero vector. -/
lemma operator_polynomial_norm_sq_integral (x : E) (p : ℝ[X]) :
    ‖polynomialVector A x p‖^2 =
      ∫ t : Icc a b, (p.eval (t : ℝ))^2
        ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) := by
  rw [← real_inner_self_eq_norm_sq, polynomial_vector_inner A hA,
    ← operator_spectral_polynomial_integral A hA a b hbounds x (p*p)]
  congr 1
  funext t
  simp only [Polynomial.eval_mul, pow_two]

/-- Concentration of the actual scalar spectral measure at one real value
forces the vector itself to be an eigenvector. -/
theorem operator_eigenvector_of_spectral_atom (r : ℝ) (x : E)
    (hatom : ∀ᵐ (t : Icc a b) ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)),
      (t : ℝ) = r) : A x = r • x := by
  let p : ℝ[X] := Polynomial.X - Polynomial.C r
  have hz : ‖polynomialVector A x p‖^2 = 0 := by
    rw [operator_polynomial_norm_sq_integral A hA a b hbounds x p]
    apply integral_eq_zero_of_ae
    filter_upwards [hatom] with t ht
    simp [p, ht]
  have hv := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
  have hp : polynomialVector A x p = A x - r • x := by
    simp [polynomialVector, p, ContinuousLinearMap.algebraMap_apply]
  rw [hp] at hv
  exact sub_eq_zero.mp hv

/-- The range of the singleton spectral projection is contained in the
corresponding actual eigenspace. -/
theorem spectral_projection_singleton_eigenvector (r : Icc a b) (x : E) :
    A (spectralProjection A hA a b hbounds {r} (measurableSet_singleton r) x) =
      (r : ℝ) • spectralProjection A hA a b hbounds {r} (measurableSet_singleton r) x := by
  apply operator_eigenvector_of_spectral_atom A hA a b hbounds
  rw [spectral_projection_measure]
  filter_upwards [ae_restrict_mem (measurableSet_singleton r)] with t ht
  exact congrArg Subtype.val (mem_singleton_iff.mp ht)

/-- A singleton spectral projection is nonzero exactly when the value is an
actual eigenvalue, so the source's projection and eigenspace formulations agree. -/
theorem spectral_projection_singleton_ne_zero_iff (r : Icc a b) :
    spectralProjection A hA a b hbounds {r} (measurableSet_singleton r) ≠ 0 ↔
      ∃ x : E, x ≠ 0 ∧ A x = (r : ℝ) • x := by
  constructor
  · intro hP
    have hex : ∃ x : E, spectralProjection A hA a b hbounds {r} (measurableSet_singleton r) x ≠ 0 := by
      by_contra hn
      apply hP
      ext x
      exact not_ne_iff.mp (not_exists.mp hn x)
    obtain ⟨x,hx⟩ := hex
    exact ⟨_, hx, spectral_projection_singleton_eigenvector A hA a b hbounds r x⟩
  · rintro ⟨x,hx,heigen⟩ hzero
    have h := spectral_projection_eigenvector A hA a b hbounds {r}
      (measurableSet_singleton r) r x heigen
    simp only [hzero, ContinuousLinearMap.zero_apply, indicator_of_mem (mem_singleton r), one_smul] at h
    exact hx h.symm

/-- The earlier scalar realization theorem is also the literal nonzero
endpoint-projection criterion from the manuscript. -/
theorem balanced_probability_realizable_iff_endpoint_projections (hab : a < b) :
    (∃ (x : E) (hx : x ≠ 0), operatorSpectralProbability A hA a b hbounds x hx =
      balancedProbability (⟨a,le_rfl,hab.le⟩ : Icc a b) ⟨b,hab.le,le_rfl⟩) ↔
    spectralProjection A hA a b hbounds {⟨a,le_rfl,hab.le⟩} (measurableSet_singleton _) ≠ 0 ∧
    spectralProjection A hA a b hbounds {⟨b,hab.le,le_rfl⟩} (measurableSet_singleton _) ≠ 0 := by
  rw [spectral_projection_singleton_ne_zero_iff, spectral_projection_singleton_ne_zero_iff]
  exact balanced_probability_realizable_iff_endpoints_eigenvalues A hA a b hab hbounds

/-- The realization criterion stated with the real Borel PVM E_A({a}) and
E_A({b}), exactly the source's notation. -/
theorem balanced_probability_realizable_iff_real_endpoint_projections (hab : a < b) :
    (∃ (x : E) (hx : x ≠ 0), operatorSpectralProbability A hA a b hbounds x hx =
      balancedProbability (⟨a,le_rfl,hab.le⟩ : Icc a b) ⟨b,hab.le,le_rfl⟩) ↔
    (operatorSpectralPVM A hA a b hbounds).map {a} (measurableSet_singleton a) ≠ 0 ∧
    (operatorSpectralPVM A hA a b hbounds).map {b} (measurableSet_singleton b) ≠ 0 := by
  rw [operator_spectral_pvm_singleton A hA a b hbounds (⟨a,le_rfl,hab.le⟩ : Icc a b),
    operator_spectral_pvm_singleton A hA a b hbounds (⟨b,hab.le,le_rfl⟩ : Icc a b)]
  exact balanced_probability_realizable_iff_endpoint_projections A hA a b hbounds hab

end BB
