import BB.OperatorMoments
import BB.RieszRepresentation

/-!
# Actual scalar spectral probabilities of bounded symmetric operators

The probability is constructed from the uniquely determined normalized moment
functional. Its existence uses exact finite Krylov compression and the proved
compact-space Riesz representation. The update below is an equality of actual
probability measures, with the density implemented by `Measure.withDensity`.
-/

namespace BB
noncomputable section
open MeasureTheory Set
open scoped Topology ENNReal NNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def operatorSpectralProbability (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) : ProbabilityMeasure (Icc a b) :=
  representingProbability (operatorMomentState A hA a b hbounds x hx)

@[simp] theorem operator_spectral_probability_functional (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) :
    probabilityFunctional (operatorSpectralProbability A hA a b hbounds x hx) =
      operatorMomentState A hA a b hbounds x hx :=
  probabilityFunctional_representing _

theorem operator_spectral_integral (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (f : C(Icc a b,ℝ)) :
    (∫ t, f t ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) =
      (operatorMomentState A hA a b hbounds x hx).1 f :=
  positiveMeasure_integral _ f

/-- Every power moment is the actual normalized operator moment. -/
theorem operator_spectral_moment (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (k : ℕ) :
    (∫ t : Icc a b, (t : ℝ)^k
      ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) =
      ⟪x,(A : E → E)^[k] x⟫/‖x‖^2 := by
  change (∫ t, ((intervalCoordinate a b)^k) t ∂(_ : Measure (Icc a b))) = _
  rw [operator_spectral_integral, operator_moment_state_power]

/-- The compact scalar spectral probability is characterized uniquely by its
operator moments; no spectral representation is assumed as a premise. -/
theorem operator_spectral_probability_unique (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (ν : ProbabilityMeasure (Icc a b))
    (hmom : ∀ k : ℕ, (∫ t : Icc a b, (t : ℝ)^k ∂(ν : Measure (Icc a b))) =
      ⟪x,(A : E → E)^[k] x⟫/‖x‖^2) :
    ν = operatorSpectralProbability A hA a b hbounds x hx := by
  apply probability_functional_injective
  rw [operator_spectral_probability_functional]
  apply positive_state_eq_of_moments
  intro k
  rw [operator_moment_state_power]
  exact hmom k

theorem operator_spectral_mean (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) :
    (∫ t : Icc a b, (t : ℝ)
      ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) =
      ⟪x,A x⟫/‖x‖^2 := by
  simpa only [pow_one,Function.iterate_one] using operator_spectral_moment A hA a b hbounds x hx 1

theorem operator_spectral_step_mass (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) :
    (∫ t, ((1-α • intervalCoordinate a b)^2 : C(Icc a b,ℝ)) t
      ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) =
      ‖operatorGradientStep A.toLinearMap α x‖^2/‖x‖^2 := by
  rw [operator_spectral_integral, operator_step_density_mass]

theorem operator_spectral_step_mass_pos (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    0 < ∫ t, ((1-α • intervalCoordinate a b)^2 : C(Icc a b,ℝ)) t
      ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
  rw [operator_spectral_step_mass]
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)) (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- The actual scalar probability of an updated vector is its normalized
squared-affine-density reweighting. -/
theorem operator_spectral_probability_reweight (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    operatorSpectralProbability A hA a b hbounds (operatorGradientStep A.toLinearMap α x) hy =
      probabilityReweight (operatorSpectralProbability A hA a b hbounds x hx)
        ((1-α • intervalCoordinate a b)^2)
        (by intro t; simp only [ContinuousMap.pow_apply]; exact sq_nonneg _)
        (operator_spectral_step_mass_pos A hA a b hbounds x hx α hy) := by
  apply probability_functional_injective
  rw [operator_spectral_probability_functional, probability_reweight_functional]
  simp only [operator_spectral_probability_functional]
  exact operator_moment_state_reweight A hA a b hbounds x hx α hy

theorem operator_spectral_step_absolutelyContinuous (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    (operatorSpectralProbability A hA a b hbounds (operatorGradientStep A.toLinearMap α x) hy :
        Measure (Icc a b)) ≪
      (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
  rw [operator_spectral_probability_reweight]
  exact normalizedReweight_absolutelyContinuous _ _

theorem operator_spectral_step_support_subset (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    measureSupport (operatorSpectralProbability A hA a b hbounds
      (operatorGradientStep A.toLinearMap α x) hy : Measure (Icc a b)) ⊆
      measureSupport (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) :=
  measureSupport_subset_of_absolutelyContinuous
    (operator_spectral_step_absolutelyContinuous A hA a b hbounds x hx α hy)

def operatorSpectralPair (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) : ProbabilityState (Icc a b) :=
  (operatorSpectralProbability A hA a b hbounds x hx,
    operatorSpectralProbability A hA a b hbounds z hz)

@[simp] theorem operator_spectral_pair_embedding (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) :
    probabilityStateEmbedding (operatorSpectralPair A hA a b hbounds x z hx hz) =
      operatorMomentPair A hA a b hbounds x z hx hz := by
  simp only [probabilityStateEmbedding,operatorSpectralPair,operatorMomentPair,
    operator_spectral_probability_functional]

theorem operator_spectral_pair_growth_sq (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) :
    probabilityGrowthSq (intervalCoordinate a b) (operatorSpectralPair A hA a b hbounds x z hx hz) =
      ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x‖^2/‖x‖^2 := by
  rw [← probability_growth_sq_embedding, operator_spectral_pair_embedding]
  exact operator_moment_pair_growth_sq A hA a b hbounds x z hx hz

theorem operator_spectral_pair_norm_ratio (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) :
    ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x‖/‖x‖ =
      probabilityGrowth (intervalCoordinate a b) (operatorSpectralPair A hA a b hbounds x z hx hz) := by
  rw [← probability_growth_embedding, operator_spectral_pair_embedding]
  exact operator_moment_pair_norm_ratio A hA a b hbounds x z hx hz

/-- The exact probability-pair recurrence for actual nonzero BB gradients. -/
theorem operator_spectral_pair_update (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0)
    (hy : operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x ≠ 0) :
    operatorSpectralPair A hA a b hbounds
      (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x) x hy hx =
      probabilityMap (intervalCoordinate a b) (operatorSpectralPair A hA a b hbounds x z hx hz) := by
  have he : probabilityStateEmbedding (operatorSpectralPair A hA a b hbounds
        (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x) x hy hx) =
      probabilityStateEmbedding (probabilityMap (intervalCoordinate a b)
        (operatorSpectralPair A hA a b hbounds x z hx hz)) := by
    rw [probability_map_embedding, operator_spectral_pair_embedding, operator_spectral_pair_embedding]
    exact operator_moment_pair_update A hA a b hbounds x z hx hz hy
  exact Prod.ext (probability_functional_injective (congrArg Prod.fst he))
    (probability_functional_injective (congrArg Prod.snd he))

/-- The unnormalized scalar spectral measure, including the zero vector. -/
def operatorSpectralMeasure (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) : FiniteMeasure (Icc a b) := by
  classical
  exact if hx : x = 0 then 0 else
    ‖x‖₊^2 •
      (operatorSpectralProbability A hA a b hbounds x hx).toFiniteMeasure

@[simp] theorem operator_spectral_measure_zero (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2) :
    operatorSpectralMeasure A hA a b hbounds (0:E) = 0 := by
  simp [operatorSpectralMeasure]

theorem operator_spectral_measure_nonzero (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) :
    (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) =
      (ENNReal.ofReal (‖x‖^2)) •
        (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
  simp only [operatorSpectralMeasure,dif_neg hx,FiniteMeasure.toMeasure_smul,
    ProbabilityMeasure.toMeasure_comp_toFiniteMeasure_eq_toMeasure]
  rw [ENNReal.smul_def]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal]
  norm_cast

theorem operator_spectral_measure_univ (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2) (x : E) :
    (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) univ =
      ENNReal.ofReal (‖x‖^2) := by
  by_cases hx : x = 0
  · subst x
    simp
  · rw [operator_spectral_measure_nonzero A hA a b hbounds x hx]
    simp

theorem operator_spectral_measure_integral (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (f : C(Icc a b,ℝ)) :
    (∫ t, f t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) =
      ‖x‖^2 * (operatorMomentState A hA a b hbounds x hx).1 f := by
  rw [operator_spectral_measure_nonzero A hA a b hbounds x hx,integral_smul_measure,
    ENNReal.toReal_ofReal (sq_nonneg _),operator_spectral_integral]
  rfl

/-- Moment identities for the unnormalized measure hold also at the zero
vector, so polarization does not need exceptional-case hypotheses. -/
theorem operator_spectral_measure_moment (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (k : ℕ) :
    (∫ t : Icc a b, (t:ℝ)^k
      ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) =
      ⟪x,(A : E → E)^[k] x⟫ := by
  by_cases hx : x = 0
  · subst x
    simp
  · change (∫ t, ((intervalCoordinate a b)^k) t ∂(_ : Measure (Icc a b))) = _
    rw [operator_spectral_measure_integral A hA a b hbounds x hx,
      operator_moment_state_power]
    have hn : ‖x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
    field_simp

end
end BB
