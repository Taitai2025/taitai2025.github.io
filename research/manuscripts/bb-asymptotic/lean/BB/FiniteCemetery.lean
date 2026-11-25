import BB.Cemetery
import BB.InvariantState
import BB.ErgodicSupport
import BB.LogCocycleInvariant
import BB.FiniteSharp

/-!
# Original finite cemetery dynamics and extended invariant averages

This file reconnects the complete finite invariant-measure classification to
the manuscript's literal isolated terminal state and minus-infinity integral.
Finite integrability and avoidance of the terminal state are conclusions,
not additional hypotheses of the final invariant-average theorem.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def finiteCemeteryMap (lam : ι → ℝ) : Cemetery (SpectralState ι) → Cemetery (SpectralState ι) :=
  killedMap (spectralMap lam) (stateGrowth lam)

def finiteCemeteryAverage (lam : ι → ℝ) (a b : ℝ)
    (μ : Measure (Cemetery (SpectralState ι))) : EReal :=
  extendedLogIntegral (killedMultiplier (stateGrowth lam)) (Real.log (1 + b / a)) μ

theorem finite_cemetery_log_upper (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (s : Cemetery (SpectralState ι)) (hs : 0 < killedMultiplier (stateGrowth lam) s) :
    Real.log (killedMultiplier (stateGrowth lam) s) ≤ Real.log (1 + b / a) := by
  cases s with
  | inl χ => exact Real.log_le_log hs (state_growth_bound lam a b ha hab hlam χ)
  | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)

theorem finite_cemetery_avoid_singular (lam : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) (μ : Measure (Cemetery (SpectralState ι)))
    [IsProbabilityMeasure μ] (hT : MeasurePreserving (finiteCemeteryMap lam) μ μ) :
    μ (Sum.inl '' {χ | stateGrowth lam χ = 0}) = 0 := by
  have he : {χ | stateGrowth lam χ = 0} = {χ | ¬ 0 < stateGrowth lam χ} := by
    ext χ
    change stateGrowth lam χ = 0 ↔ ¬ 0 < stateGrowth lam χ
    exact ⟨fun h => by rw [h]; exact lt_irrefl 0,
      fun h => le_antisymm (not_lt.mp h) (state_growth_nonneg lam χ)⟩
  rw [he]
  exact killed_invariant_singular_null (spectralMap lam) (stateGrowth lam)
    (state_growth_continuous lam a ha hlam).measurable μ hT

theorem finite_cemetery_avoid_terminal (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (μ : Measure (Cemetery (SpectralState ι))) [IsProbabilityMeasure μ]
    (hfinite : finiteCemeteryAverage lam a b μ ≠ ⊥) : μ {cemeteryPoint} = 0 := by
  have hr := (state_growth_continuous lam a ha (fun i => (hlam i).1)).measurable
  have hp := (extendedLogIntegral_finite_reduction _ (killedMultiplier_measurable _ hr)
    _ (finite_cemetery_log_upper lam a b ha hab hlam) μ hfinite).1
  apply measure_mono_null (t := {s | ¬ 0 < killedMultiplier (stateGrowth lam) s})
  · intro s hs
    rw [Set.mem_singleton_iff] at hs
    subst s
    exact lt_irrefl 0
  · exact ae_iff.mp hp

/-- The full extended-valued invariant bound, including all terminal and
nonintegrable cases. -/
theorem finite_cemetery_invariant_bound [Nonempty ι]
    (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (μ : Measure (Cemetery (SpectralState ι))) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (finiteCemeteryMap lam) μ μ) :
    finiteCemeteryAverage lam a b μ ≤ (Real.log (rate a b) : EReal) := by
  have hr := (state_growth_continuous lam a ha (fun i => (hlam i).1)).measurable
  rcases extendedLogIntegral_dichotomy _ (killedMultiplier_measurable _ hr) _
      (finite_cemetery_log_upper lam a b ha hab hlam) μ with hbot | ⟨hp,hf,he⟩
  · change extendedLogIntegral _ _ μ ≤ _
    rw [hbot]
    exact bot_le
  · let χ₀ : SpectralState ι := Classical.choice inferInstance
    let ν := cemeteryBaseMeasure χ₀ μ
    have hνT := cemetery_base_preserving (spectralMap lam) (stateGrowth lam)
      (spectral_map_measurable lam a ha (fun i => (hlam i).1)) χ₀ μ hT hp
    have hνr := cemetery_base_regular (stateGrowth lam) hr χ₀ μ hp
    have htransfer := cemetery_log_integrable_transfer (stateGrowth lam) hr χ₀ μ hp hf
    have hνR : ∀ᵐ χ ∂ν, 0 < stateGrowthSq lam χ := by
      filter_upwards [hνr] with χ hχ
      exact Real.sqrt_pos.mp hχ
    have hb := spectral_state_invariant_bound lam a b ha hlam ν hνT hνR htransfer.1
    change extendedLogIntegral _ _ μ ≤ _
    rw [he, htransfer.2]
    exact EReal.coe_le_coe_iff.mpr hb

/-- Uniqueness on the original cemetery state space, with no assumed
regularity or integrability premise. -/
theorem finite_cemetery_unique_maximizer
    (lam : ι → ℝ) (hinj : Function.Injective lam) (lo hi : ι) (hne : lo ≠ hi)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (μ : Measure (Cemetery (SpectralState ι))) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (finiteCemeteryMap lam) μ μ)
    (hmaximal : finiteCemeteryAverage lam a b μ = (Real.log (rate a b) : EReal)) :
    μ = Measure.dirac (Sum.inl (balancedSpectralState lo hi hne)) := by
  have hr := (state_growth_continuous lam a ha (fun i => (hlam i).1)).measurable
  have hfinite : finiteCemeteryAverage lam a b μ ≠ ⊥ :=
    hmaximal.trans_ne (EReal.coe_ne_bot _)
  obtain ⟨hp,hf,he⟩ := extendedLogIntegral_finite_reduction _ (killedMultiplier_measurable _ hr)
    _ (finite_cemetery_log_upper lam a b ha hab.le hlam) μ hfinite
  let χ₀ := balancedSpectralState lo hi hne
  let ν := cemeteryBaseMeasure χ₀ μ
  have hνT := cemetery_base_preserving (spectralMap lam) (stateGrowth lam)
    (spectral_map_measurable lam a ha (fun i => (hlam i).1)) χ₀ μ hT hp
  have hνr := cemetery_base_regular (stateGrowth lam) hr χ₀ μ hp
  have htransfer := cemetery_log_integrable_transfer (stateGrowth lam) hr χ₀ μ hp hf
  have hνR : ∀ᵐ χ ∂ν, 0 < stateGrowthSq lam χ := by
    filter_upwards [hνr] with χ hχ
    exact Real.sqrt_pos.mp hχ
  have hνmax : (∫ χ, Real.log (stateGrowth lam χ) ∂ν) = Real.log (rate a b) := by
    apply EReal.coe_injective
    rw [← htransfer.2, ← he]
    exact hmaximal
  have hνeq := spectral_state_unique_maximizer lam hinj lo hi hne a b ha hab hlo hhi hlam
    ν hνT hνR htransfer.1 hνmax
  rw [← cemetery_base_lift (stateGrowth lam) χ₀ μ hp]
  change ν.map Sum.inl = _
  rw [hνeq, Measure.map_dirac measurable_inl]

theorem finite_cemetery_balanced_invariant
    (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) (hab : lam lo < lam hi) :
    MeasurePreserving (finiteCemeteryMap lam)
      (Measure.dirac (Sum.inl (balancedSpectralState lo hi hne)))
      (Measure.dirac (Sum.inl (balancedSpectralState lo hi hne))) := by
  have hr := (state_growth_continuous lam a ha hlam).measurable
  have hT := killedMap_measurable (spectralMap lam) (stateGrowth lam)
    (spectral_map_measurable lam a ha hlam) hr
  have hpos : 0 < stateGrowth lam (balancedSpectralState lo hi hne) := by
    rw [balanced_growth lam lo hi hne (ha.trans_le (hlam lo)) hab]
    exact rate_pos (ha.trans_le (hlam lo)) hab
  refine ⟨hT, ?_⟩
  change (Measure.dirac _).map (killedMap _ _) = _
  rw [Measure.map_dirac hT]
  congr 1
  change killedMap _ _ _ = _
  rw [killedMap_regular _ _ _ hpos,
    balanced_spectral_fixed lam lo hi hne (ha.trans_le (hlam lo)) hab]

theorem finite_cemetery_balanced_average
    (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    finiteCemeteryAverage lam a b
      (Measure.dirac (Sum.inl (balancedSpectralState lo hi hne))) =
      (Real.log (rate a b) : EReal) := by
  have hr := (state_growth_continuous lam a ha (fun i => (hlam i).1)).measurable
  have hb : stateGrowth lam (balancedSpectralState lo hi hne) = rate a b := by
    simpa only [hlo,hhi] using balanced_growth lam lo hi hne (by simpa only [hlo] using ha)
      (by simpa only [hlo,hhi] using hab)
  have hp : ∀ᵐ s ∂Measure.dirac (Sum.inl (balancedSpectralState lo hi hne)),
      0 < killedMultiplier (stateGrowth lam) s := by
    rw [ae_dirac_eq]
    change 0 < stateGrowth lam (balancedSpectralState lo hi hne)
    rw [hb]
    exact rate_pos ha hab
  have hf : Integrable (fun s => Real.log (killedMultiplier (stateGrowth lam) s))
      (Measure.dirac (Sum.inl (balancedSpectralState lo hi hne))) :=
    (integrable_const _).congr (ae_eq_dirac _).symm
  rw [finiteCemeteryAverage, extendedLogIntegral_of_integrable _
    (killedMultiplier_measurable _ hr) _ (finite_cemetery_log_upper lam a b ha hab.le hlam) _ hp hf,
    integral_dirac]
  simp only [killedMultiplier, Sum.elim_inl, hb]

def positiveSpectralFace (J : Finset ι) : Set (SpectralState ι) :=
  {χ | (∀ i, χ.1.1 i ≠ 0 ↔ i ∈ J) ∧ (∀ i, χ.2.1 i ≠ 0 ↔ i ∈ J)}

theorem positive_spectral_face_measurable (J : Finset ι) :
    MeasurableSet (positiveSpectralFace J) := by
  exact (supportClass_measurable (fun χ : SpectralState ι => χ.1.1)
    (fun i => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).measurable) J).inter
    (supportClass_measurable (fun χ : SpectralState ι => χ.2.1)
    (fun i => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).measurable) J)

/-- Source `lem:support-face` on the original isolated-terminal state space. -/
theorem finite_cemetery_ergodic_support [Nonempty ι]
    (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (μ : Measure (Cemetery (SpectralState ι))) [IsProbabilityMeasure μ]
    (hT : Ergodic (finiteCemeteryMap lam) μ)
    (hfinite : finiteCemeteryAverage lam a b μ ≠ ⊥) :
    ∃ J : Finset ι, 2 ≤ J.card ∧ μ (Sum.inl '' positiveSpectralFace J) = 1 := by
  let χ₀ : SpectralState ι := Classical.choice inferInstance
  let π := cemeteryProjection χ₀
  let w : Cemetery (SpectralState ι) → ι → ℝ := fun s => (π s).1.1
  let z : Cemetery (SpectralState ι) → ι → ℝ := fun s => (π s).2.1
  have hπ := cemeteryProjection_measurable χ₀
  have hwmeas : ∀ i, Measurable (fun s => w s i) := fun i =>
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).measurable).comp hπ
  have hzmeas : ∀ i, Measurable (fun s => z s i) := fun i =>
    (((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).measurable).comp hπ
  have hr := (state_growth_continuous lam a ha (fun i => (hlam i).1)).measurable
  obtain ⟨hp,_,_⟩ := extendedLogIntegral_finite_reduction _ (killedMultiplier_measurable _ hr)
    _ (finite_cemetery_log_upper lam a b ha hab hlam) μ hfinite
  have hreg : ∀ᵐ s ∂μ, 0 < growthSq lam (w s) (z s) := by
    filter_upwards [hp] with s hs
    cases s with
    | inl χ => exact Real.sqrt_pos.mp hs
    | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)
  have hup : ∀ᵐ s ∂μ, w (finiteCemeteryMap lam s) = weightUpdate lam (w s) (z s) := by
    filter_upwards [hp] with s hs
    cases s with
    | inl χ =>
      change (cemeteryProjection χ₀ (killedMap _ _ (Sum.inl χ))).1.1 = _
      rw [killedMap_regular (spectralMap lam) (stateGrowth lam) χ hs]
      exact (spectral_map_regular lam χ (Real.sqrt_pos.mp hs)).1
    | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)
  have hshift : ∀ᵐ s ∂μ, z (finiteCemeteryMap lam s) = w s := by
    filter_upwards [hp] with s hs
    cases s with
    | inl χ =>
      change (cemeteryProjection χ₀ (killedMap _ _ (Sum.inl χ))).2.1 = _
      rw [killedMap_regular (spectralMap lam) (stateGrowth lam) χ hs]
      exact congrArg Subtype.val (spectral_map_regular lam χ (Real.sqrt_pos.mp hs)).2
    | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)
  obtain ⟨J,hJ,hface⟩ := ergodic_bb_common_support μ (finiteCemeteryMap lam) hT lam
    (fun i => ha.trans_le (hlam i).1) w z (fun s => (π s).1.2) (fun s => (π s).2.2)
    hwmeas hzmeas hreg hup hshift
  refine ⟨J,hJ,(mem_ae_iff_prob_eq_one
    (measurableSet_inl_image.mpr (positive_spectral_face_measurable J))).mp ?_⟩
  filter_upwards [hp,hface] with s hs hf
  cases s with
  | inl χ => exact ⟨χ,hf,rfl⟩
  | inr u => exact False.elim ((lt_irrefl (0 : ℝ)) hs)

/-- The source additive estimate on every nonterminal cemetery orbit segment. -/
theorem finite_cemetery_semiuniform (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (η : ℝ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n s,
      (∀ j < n, 0 < killedMultiplier (stateGrowth lam) ((finiteCemeteryMap lam)^[j] s)) →
      (∑ j in Finset.range n,
        Real.log (killedMultiplier (stateGrowth lam) ((finiteCemeteryMap lam)^[j] s))) ≤
        (n : ℝ) * (Real.log (rate a b) + η) + B := by
  classical
  apply semiuniform_log_sum_of_all_envelopes _ _ (rate a b) (rate_pos ha hab) _ η hη
  exact killed_all_prefix_envelopes (spectralMap lam) (stateGrowth lam) (state_growth_nonneg lam)
    (rate a b) (rate_pos ha hab).le
    (fun γ hγ => finite_spectral_envelope lam a b γ ha hab.le hlam hγ)

def finiteCemeteryAverages (lam : ι → ℝ) (a b : ℝ) : Set EReal :=
  {v | ∃ μ : Measure (Cemetery (SpectralState ι)), IsProbabilityMeasure μ ∧
    MeasurePreserving (finiteCemeteryMap lam) μ μ ∧ finiteCemeteryAverage lam a b μ = v}

/-- The supremum is attained, with all extended averages included. -/
theorem finite_cemetery_maximum
    (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    IsGreatest (finiteCemeteryAverages lam a b) (Real.log (rate a b) : EReal) := by
  letI : Nonempty ι := ⟨lo⟩
  constructor
  · refine ⟨Measure.dirac (Sum.inl (balancedSpectralState lo hi hne)),inferInstance,?_,?_⟩
    · exact finite_cemetery_balanced_invariant lam lo hi hne a ha (fun i => (hlam i).1)
        (by simpa only [hlo,hhi] using hab)
    · exact finite_cemetery_balanced_average lam lo hi hne a b ha hab hlo hhi hlam
  · rintro v ⟨μ,hμ,hT,he⟩
    letI : IsProbabilityMeasure μ := hμ
    rw [← he]
    exact finite_cemetery_invariant_bound lam a b ha hab.le hlam μ hT

end BB
