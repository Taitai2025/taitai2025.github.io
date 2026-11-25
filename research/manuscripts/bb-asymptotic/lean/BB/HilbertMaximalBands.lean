import BB.HilbertCoordinateRestriction
import BB.HilbertBandCertificate

/-!
# Endpoint-band positivity for every maximal invariant law

This argument does not use ergodic decomposition. A zero endpoint-band event
forces both consecutive measures into a strictly smaller spectral interval.
Its invariant restriction has a strictly smaller average by clipping the
coordinate, so exact averaging forces the event to have zero mass.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

lemma maximal_coordinate_range_event_null (lam : C(K,ℝ)) (A B a b : ℝ)
    (hA : 0 < A) (hAB : A < B) (hlam : ∀ x, A ≤ lam x ∧ lam x ≤ B)
    (ha : 0 < a) (hab : a < b) (hrate : rate a b < rate A B)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate A B)) :
    μ {χ | InCoordinateRange lam a b χ} = 0 := by
  let E : Set (ProbabilityState K) := {χ | InCoordinateRange lam a b χ}
  have hE : MeasurableSet E := coordinate_range_measurable lam a b
  have hEforward : E ⊆ probabilityMap lam ⁻¹' E :=
    fun χ hχ => probability_map_preserves_coordinate_range lam a b χ hχ
  have hEinv := invariant_event_of_forward_closed μ (probabilityMap lam) hT E hE hEforward
  have hEcinv : Eᶜ =ᵐ[μ] probabilityMap lam ⁻¹' Eᶜ := by
    filter_upwards [hEinv] with χ hχ
    exact congrArg Not hχ
  have hTE := measurePreserving_restrict_invariant μ (probabilityMap lam) hT E hE hEinv
  have hTEc := measurePreserving_restrict_invariant μ (probabilityMap lam) hT Eᶜ hE.compl hEcinv
  have hpart := probability_invariant_local_range_bound lam a b ha hab (μ.restrict E) hTE
    (ae_restrict_of_ae hregular) (ae_restrict_mem hE) hf.restrict
  have hcompl := probability_finite_invariant_bound lam A B hA hAB hlam (μ.restrict Eᶜ) hTEc
    (ae_restrict_of_ae hregular) hf.restrict
  simp only [Measure.restrict_apply_univ] at hpart hcompl
  exact strict_component_null_of_maximal_mean μ E hE _ hf (Real.log (rate A B)) (Real.log (rate a b))
    (Real.log_lt_log (rate_pos ha hab) hrate) hmaximal hpart hcompl

lemma probability_maximal_lower_band_positive (lam : C(K,ℝ)) (a b δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hδd : δ < b-a)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    ∀ᵐ χ ∂μ, 0 < probabilityBandMass χ.1 (lowerSpectralBand lam a δ) := by
  have haδ : 0 < a+δ := add_pos ha hδ
  have hlocal : a+δ < b := by linarith
  have hratele : rate (a+δ) b ≤ rate a b := rate_mono_interval ha (by linarith) hlocal.le le_rfl
  have hraten : rate (a+δ) b ≠ rate a b := by
    intro heq
    have h := (rate_eq_of_nested_iff ha (by linarith : a ≤ a+δ) hlocal le_rfl).mp heq
    linarith only [h.1,hδ]
  have hrate : rate (a+δ) b < rate a b := hratele.lt_of_ne hraten
  have hzero := maximal_coordinate_range_event_null lam a b (a+δ) b ha hab hlam haδ hlocal hrate
    μ hT hregular hf hmaximal
  have hnot : ∀ᵐ χ ∂μ, ¬ InCoordinateRange lam (a+δ) b χ := by
    apply ae_iff.mpr
    simpa only [not_not] using hzero
  let O : Set K := {x | lam x < a+δ}
  have hO : IsOpen O := isOpen_lt lam.continuous continuous_const
  have hconsecutive := probability_consecutive_zero_events lam μ hT hregular O hO
  filter_upwards [hnot,hconsecutive] with χ hn hc
  apply (probability_band_mass_pos_iff χ.1 _).mpr
  intro hz
  have hOzero : (χ.1 : Measure K) O = 0 := measure_mono_null
    (show O ⊆ lowerSpectralBand lam a δ from
      fun x hx => ⟨(hlam x).1,(show lam x < a+δ from hx).le⟩) hz
  have hOzero' := hc.mp hOzero
  have hν : ∀ᵐ x ∂(χ.1 : Measure K), a+δ ≤ lam x := by
    apply ae_iff.mpr
    simpa only [not_le] using hOzero
  have hζ : ∀ᵐ x ∂(χ.2 : Measure K), a+δ ≤ lam x := by
    apply ae_iff.mpr
    simpa only [not_le] using hOzero'
  exact hn ⟨hν.mono (fun x hx => ⟨hx,(hlam x).2⟩),hζ.mono (fun x hx => ⟨hx,(hlam x).2⟩)⟩

lemma probability_maximal_upper_band_positive (lam : C(K,ℝ)) (a b δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hδd : δ < b-a)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    ∀ᵐ χ ∂μ, 0 < probabilityBandMass χ.1 (upperSpectralBand lam b δ) := by
  have hlocal : a < b-δ := by linarith
  have hratele : rate a (b-δ) ≤ rate a b := rate_mono_interval ha le_rfl hlocal.le (by linarith)
  have hraten : rate a (b-δ) ≠ rate a b := by
    intro heq
    have h := (rate_eq_of_nested_iff ha le_rfl hlocal (by linarith : b-δ ≤ b)).mp heq
    linarith only [h.2,hδ]
  have hrate : rate a (b-δ) < rate a b := hratele.lt_of_ne hraten
  have hzero := maximal_coordinate_range_event_null lam a b a (b-δ) ha hab hlam ha hlocal hrate
    μ hT hregular hf hmaximal
  have hnot : ∀ᵐ χ ∂μ, ¬ InCoordinateRange lam a (b-δ) χ := by
    apply ae_iff.mpr
    simpa only [not_not] using hzero
  let O : Set K := {x | b-δ < lam x}
  have hO : IsOpen O := isOpen_lt continuous_const lam.continuous
  have hconsecutive := probability_consecutive_zero_events lam μ hT hregular O hO
  filter_upwards [hnot,hconsecutive] with χ hn hc
  apply (probability_band_mass_pos_iff χ.1 _).mpr
  intro hz
  have hOzero : (χ.1 : Measure K) O = 0 := measure_mono_null
    (show O ⊆ upperSpectralBand lam b δ from
      fun x hx => ⟨(show b-δ < lam x from hx).le,(hlam x).2⟩) hz
  have hOzero' := hc.mp hOzero
  have hν : ∀ᵐ x ∂(χ.1 : Measure K), lam x ≤ b-δ := by
    apply ae_iff.mpr
    simpa only [not_le] using hOzero
  have hζ : ∀ᵐ x ∂(χ.2 : Measure K), lam x ≤ b-δ := by
    apply ae_iff.mpr
    simpa only [not_le] using hOzero'
  exact hn ⟨hν.mono (fun x hx => ⟨(hlam x).1,hx⟩),hζ.mono (fun x hx => ⟨(hlam x).1,hx⟩)⟩

theorem probability_maximal_endpoint_bands_positive (lam : C(K,ℝ)) (a b δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ) (hδd : δ < b-a)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    ∀ᵐ χ ∂μ, 0 < probabilityBandMass χ.1 (lowerSpectralBand lam a δ) ∧
      0 < probabilityBandMass χ.1 (upperSpectralBand lam b δ) :=
  (probability_maximal_lower_band_positive lam a b δ ha hab hδ hδd hlam μ hT hregular hf hmaximal).and
    (probability_maximal_upper_band_positive lam a b δ ha hab hδ hδd hlam μ hT hregular hf hmaximal)

end BB
