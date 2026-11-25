import BB.HilbertPersistentSupport
import BB.InvariantRestriction

/-!
# Restricting an invariant law to a smaller spectral interval

A continuous clipped coordinate agrees almost everywhere with the original
coordinate whenever both probability measures are carried by the smaller
interval. Actual means, multiplier integrals, and reweighted measures then
agree. This permits invariant averaging on smaller intervals without an
ergodic decomposition or an assumed spectral measure disintegration.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

lemma probability_reweight_congr_ae (ν : ProbabilityMeasure K) (q q' : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (hq' : ∀ x, 0 ≤ q' x)
    (hreg : 0 < ∫ x, q x ∂(ν : Measure K)) (hreg' : 0 < ∫ x, q' x ∂(ν : Measure K))
    (heq : q =ᵐ[(ν : Measure K)] q') :
    probabilityReweight ν q hq hreg = probabilityReweight ν q' hq' hreg' := by
  apply Subtype.ext
  change normalizedReweight (ν : Measure K) (fun x => ENNReal.ofReal (q x)) =
    normalizedReweight (ν : Measure K) (fun x => ENNReal.ofReal (q' x))
  have hden : (fun x => ENNReal.ofReal (q x)) =ᵐ[(ν : Measure K)] (fun x => ENNReal.ofReal (q' x)) :=
    heq.mono (fun _ hx => congrArg ENNReal.ofReal hx)
  unfold normalizedReweight
  rw [lintegral_congr_ae hden,withDensity_congr_ae hden]

lemma probability_mean_coordinate_congr (lam lam' : C(K,ℝ)) (χ : ProbabilityState K)
    (hζ : lam =ᵐ[(χ.2 : Measure K)] lam') : probabilityMean lam χ = probabilityMean lam' χ :=
  integral_congr_ae hζ

lemma probability_growth_sq_coordinate_congr (lam lam' : C(K,ℝ)) (χ : ProbabilityState K)
    (hν : lam =ᵐ[(χ.1 : Measure K)] lam') (hζ : lam =ᵐ[(χ.2 : Measure K)] lam') :
    probabilityGrowthSq lam χ = probabilityGrowthSq lam' χ := by
  have hm := probability_mean_coordinate_congr lam lam' χ hζ
  apply integral_congr_ae
  filter_upwards [hν] with x hx
  rw [hx,hm]

lemma probability_growth_coordinate_congr (lam lam' : C(K,ℝ)) (χ : ProbabilityState K)
    (hν : lam =ᵐ[(χ.1 : Measure K)] lam') (hζ : lam =ᵐ[(χ.2 : Measure K)] lam') :
    probabilityGrowth lam χ = probabilityGrowth lam' χ :=
  congrArg Real.sqrt (probability_growth_sq_coordinate_congr lam lam' χ hν hζ)

lemma probability_map_coordinate_congr (lam lam' : C(K,ℝ)) (χ : ProbabilityState K)
    (hν : lam =ᵐ[(χ.1 : Measure K)] lam') (hζ : lam =ᵐ[(χ.2 : Measure K)] lam') :
    probabilityMap lam χ = probabilityMap lam' χ := by
  have hm := probability_mean_coordinate_congr lam lam' χ hζ
  have hR := probability_growth_sq_coordinate_congr lam lam' χ hν hζ
  have hq : quadraticMultiplier lam (probabilityMean lam χ) =ᵐ[(χ.1 : Measure K)]
      quadraticMultiplier lam' (probabilityMean lam' χ) := by
    filter_upwards [hν] with x hx
    simp only [quadraticMultiplier_apply,hx,hm]
  by_cases hr : 0 < probabilityGrowthSq lam χ
  · have hr' : 0 < probabilityGrowthSq lam' χ := hR ▸ hr
    rw [probabilityMap,dif_pos hr,probabilityMap,dif_pos hr']
    apply Prod.ext
    · exact probability_reweight_congr_ae χ.1 _ _
        (quadraticMultiplier_nonneg lam _) (quadraticMultiplier_nonneg lam' _)
        (by simpa only [quadraticMultiplier_apply,probabilityGrowthSq] using hr)
        (by simpa only [quadraticMultiplier_apply,probabilityGrowthSq] using hr') hq
    · rfl
  · simp only [probabilityMap,← hR,hr,dif_neg,not_false_eq_true]

def clippedCoordinate (lam : C(K,ℝ)) (a b : ℝ) : C(K,ℝ) :=
  ⟨fun x => min b (max a (lam x)), continuous_const.min (continuous_const.max lam.continuous)⟩

lemma clipped_coordinate_bounds (lam : C(K,ℝ)) (a b : ℝ) (hab : a ≤ b) :
    ∀ x, a ≤ clippedCoordinate lam a b x ∧ clippedCoordinate lam a b x ≤ b := by
  intro x
  exact ⟨le_min hab (le_max_left _ _),min_le_left _ _⟩

lemma clipped_coordinate_eq (lam : C(K,ℝ)) (a b : ℝ) (x : K)
    (hx : a ≤ lam x ∧ lam x ≤ b) : clippedCoordinate lam a b x = lam x := by
  simp only [clippedCoordinate,ContinuousMap.coe_mk,max_eq_right hx.1,min_eq_right hx.2]

def InCoordinateRange (lam : C(K,ℝ)) (a b : ℝ) (χ : ProbabilityState K) : Prop :=
  (∀ᵐ x ∂(χ.1 : Measure K), a ≤ lam x ∧ lam x ≤ b) ∧
    (∀ᵐ x ∂(χ.2 : Measure K), a ≤ lam x ∧ lam x ≤ b)

lemma clipped_coordinate_agrees_on_range (lam : C(K,ℝ)) (a b : ℝ) (χ : ProbabilityState K)
    (hχ : InCoordinateRange lam a b χ) :
    probabilityMap (clippedCoordinate lam a b) χ = probabilityMap lam χ ∧
      probabilityGrowth (clippedCoordinate lam a b) χ = probabilityGrowth lam χ := by
  have hν : clippedCoordinate lam a b =ᵐ[(χ.1 : Measure K)] lam :=
    hχ.1.mono (fun x hx => clipped_coordinate_eq lam a b x hx)
  have hζ : clippedCoordinate lam a b =ᵐ[(χ.2 : Measure K)] lam :=
    hχ.2.mono (fun x hx => clipped_coordinate_eq lam a b x hx)
  exact ⟨probability_map_coordinate_congr _ _ χ hν hζ,probability_growth_coordinate_congr _ _ χ hν hζ⟩

lemma probability_map_preserves_coordinate_range (lam : C(K,ℝ)) (a b : ℝ) (χ : ProbabilityState K)
    (hχ : InCoordinateRange lam a b χ) : InCoordinateRange lam a b (probabilityMap lam χ) := by
  by_cases hr : 0 < probabilityGrowthSq lam χ
  · constructor
    · exact (probability_map_first_absolutelyContinuous lam χ).ae_le hχ.1
    · simpa only [probabilityMap,dif_pos hr] using hχ.1
  · simpa only [probabilityMap,dif_neg hr] using hχ

section Invariant
variable [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

lemma coordinate_range_measurable (lam : C(K,ℝ)) (a b : ℝ) :
    MeasurableSet {χ : ProbabilityState K | InCoordinateRange lam a b χ} := by
  let O : Set K := (lam ⁻¹' Icc a b)ᶜ
  have hO : IsOpen O := (isClosed_Icc.preimage lam.continuous).isOpen_compl
  have hfirst : Measurable (fun χ : ProbabilityState K => (χ.1 : Measure K) O) :=
    ((probability_open_mass_lowerSemicontinuous O hO).comp_continuous continuous_fst).measurable
  have hsecond : Measurable (fun χ : ProbabilityState K => (χ.2 : Measure K) O) :=
    ((probability_open_mass_lowerSemicontinuous O hO).comp_continuous continuous_snd).measurable
  have hnull := (hfirst (measurableSet_singleton 0)).inter (hsecond (measurableSet_singleton 0))
  convert hnull using 1

lemma probability_consecutive_zero_events (lam : C(K,ℝ))
    (μ : Measure (ProbabilityState K)) [IsFiniteMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ) (B : Set K) (hB : IsOpen B) :
    ∀ᵐ χ ∂μ, (χ.1 : Measure K) B = 0 ↔ (χ.2 : Measure K) B = 0 := by
  let A : Set (ProbabilityState K) := {χ | (χ.1 : Measure K) B = 0}
  have hfirst : Measurable (fun χ : ProbabilityState K => (χ.1 : Measure K) B) :=
    ((probability_open_mass_lowerSemicontinuous B hB).comp_continuous continuous_fst).measurable
  have hsecond : Measurable (fun χ : ProbabilityState K => (χ.2 : Measure K) B) :=
    ((probability_open_mass_lowerSemicontinuous B hB).comp_continuous continuous_snd).measurable
  have hA : MeasurableSet A := hfirst (measurableSet_singleton 0)
  have hforward : A ⊆ probabilityMap lam ⁻¹' A :=
    fun χ hχ => probability_map_first_absolutelyContinuous lam χ hχ
  have hinv := invariant_event_of_forward_closed μ (probabilityMap lam) hT A hA hforward
  have hafter : ∀ᵐ χ ∂μ, ((probabilityMap lam χ).1 : Measure K) B = 0 ↔
      ((probabilityMap lam χ).2 : Measure K) B = 0 := by
    filter_upwards [hinv,hregular] with χ hi hr
    have hR : 0 < probabilityGrowthSq lam χ := Real.sqrt_pos.mp hr
    have hshift : (probabilityMap lam χ).2 = χ.1 := by rw [probabilityMap,dif_pos hR]
    rw [hshift]
    exact (Iff.of_eq hi).symm
  have hmeas : MeasurableSet {χ : ProbabilityState K | (χ.1 : Measure K) B = 0 ↔ (χ.2 : Measure K) B = 0} :=
    ((hfirst (measurableSet_singleton 0)).mem.iff (hsecond (measurableSet_singleton 0)).mem).setOf
  have hmap := (ae_map_iff hT.measurable.aemeasurable hmeas).mpr hafter
  rwa [hT.map_eq] at hmap

lemma probability_finite_invariant_bound (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsFiniteMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ) :
    (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) ≤ (μ univ).toReal * Real.log (rate a b) := by
  apply invariant_finite_bound_of_probability_bound (probabilityMap lam)
    (fun χ => 0 < probabilityGrowth lam χ) _ _ ?_ μ hT hregular hf
  intro ν hνprob hνT hνreg hνf
  letI : IsProbabilityMeasure ν := hνprob
  exact invariant_log_integral_le_of_all_envelopes ν (probabilityMap lam) hνT
    (probabilityGrowth lam) hνreg hνf (rate a b) (rate_pos ha hab)
    (fun γ hγ => probability_prefix_envelope lam a b γ ha hab.le hlam hγ)

lemma probability_invariant_local_range_bound (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b)
    (μ : Measure (ProbabilityState K)) [IsFiniteMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hrange : ∀ᵐ χ ∂μ, InCoordinateRange lam a b χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ) :
    (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) ≤ (μ univ).toReal * Real.log (rate a b) := by
  let lam' := clippedCoordinate lam a b
  have hmap : probabilityMap lam' =ᵐ[μ] probabilityMap lam :=
    hrange.mono (fun χ hχ => (clipped_coordinate_agrees_on_range lam a b χ hχ).1)
  have hgrowth : probabilityGrowth lam' =ᵐ[μ] probabilityGrowth lam :=
    hrange.mono (fun χ hχ => (clipped_coordinate_agrees_on_range lam a b χ hχ).2)
  have hlog : (fun χ => Real.log (probabilityGrowth lam' χ)) =ᵐ[μ]
      (fun χ => Real.log (probabilityGrowth lam χ)) := hgrowth.mono (fun _ hx => congrArg Real.log hx)
  have hT' : MeasurePreserving (probabilityMap lam') μ μ :=
    ⟨probability_map_measurable lam' a ha (fun x => (clipped_coordinate_bounds lam a b hab.le x).1),
      (Measure.map_congr hmap).trans hT.map_eq⟩
  have hreg' : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam' χ := by
    filter_upwards [hregular,hgrowth] with χ hr hg
    rwa [hg]
  have hf' := hf.congr hlog.symm
  have hbnd := probability_finite_invariant_bound lam' a b ha hab
    (clipped_coordinate_bounds lam a b hab.le) μ hT' hreg' hf'
  rwa [integral_congr_ae hlog] at hbnd

end Invariant
end BB
