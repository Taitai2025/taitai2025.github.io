import BB.HilbertMaximalRigidity
import BB.BalancedProbability

/-!
# The original Hilbert probability-state maximal invariant law

The final statements use the isolated terminal state and a genuine
extended-real logarithmic integral. Regularity and real integrability follow
from a finite maximizing average. Uniqueness is proved for every invariant
law directly, without an ergodic decomposition assumption.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

theorem probability_state_unique_maximizer (lam : C(K,ℝ)) (hinj : Function.Injective lam)
    (xa xb : K) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    μ = Measure.dirac (balancedProbabilityState xa xb) := by
  have hrigid := probability_maximal_rigidity lam a b ha hab hlam μ hT hregular hf hmaximal
  have hfirst : ∀ᵐ χ ∂μ, χ.1 = balancedProbability xa xb := by
    filter_upwards [hrigid] with χ hχ
    exact probability_eq_balanced_of_endpoints_mean χ.1 lam hinj xa xb a b hab hxa hxb hχ.2.2.2 hχ.2.1
  have hsecondT : ∀ᵐ χ ∂μ, (probabilityMap lam χ).2 = balancedProbability xa xb := by
    filter_upwards [hfirst,hregular] with χ hχ hr
    have hR : 0 < probabilityGrowthSq lam χ := Real.sqrt_pos.mp hr
    simpa only [probabilityMap,dif_pos hR] using hχ
  have hsecondMeas : MeasurableSet {χ : ProbabilityState K | χ.2 = balancedProbability xa xb} :=
    (isClosed_eq continuous_snd continuous_const).measurableSet
  have hsecond : ∀ᵐ χ ∂μ, χ.2 = balancedProbability xa xb := by
    have hmap := (ae_map_iff hT.measurable.aemeasurable hsecondMeas).mpr hsecondT
    rwa [hT.map_eq] at hmap
  have heq : (fun χ : ProbabilityState K => χ) =ᵐ[μ] (fun _ => balancedProbabilityState xa xb) := by
    filter_upwards [hfirst,hsecond] with χ h₁ h₂
    exact Prod.ext h₁ h₂
  calc
    μ = μ.map (fun χ => χ) := Measure.map_id'.symm
    _ = μ.map (fun _ => balancedProbabilityState xa xb) := Measure.map_congr heq
    _ = Measure.dirac (balancedProbabilityState xa xb) := by
      rw [Measure.map_const,measure_univ,one_smul]

def probabilityCemeteryMap (lam : C(K,ℝ)) : Cemetery (ProbabilityState K) → Cemetery (ProbabilityState K) :=
  killedMap (probabilityMap lam) (probabilityGrowth lam)

def probabilityCemeteryAverage (lam : C(K,ℝ)) (a b : ℝ)
    (μ : Measure (Cemetery (ProbabilityState K))) : EReal :=
  extendedLogIntegral (killedMultiplier (probabilityGrowth lam)) (Real.log (1+b/a)) μ

lemma probability_cemetery_log_upper (lam : C(K,ℝ)) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (χ : Cemetery (ProbabilityState K)) (hχ : 0 < killedMultiplier (probabilityGrowth lam) χ) :
    Real.log (killedMultiplier (probabilityGrowth lam) χ) ≤ Real.log (1+b/a) := by
  cases χ with
  | inl ξ => exact Real.log_le_log hχ (probability_growth_bound lam a b ha hab hlam ξ)
  | inr u => exact (lt_irrefl (0:ℝ) hχ).elim

theorem probability_cemetery_invariant_bound (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (Cemetery (ProbabilityState K))) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityCemeteryMap lam) μ μ) :
    probabilityCemeteryAverage lam a b μ ≤ (Real.log (rate a b) : EReal) :=
  probability_hilbert_invariant_bound lam a b ha hab hlam μ hT

/-- Literal isolated-terminal uniqueness. The only analytic hypotheses are
the compact spectral domain, distinct positive endpoints, and invariance.
No additional regularity, integrability, or ergodicity premise is present. -/
theorem probability_cemetery_unique_maximizer (lam : C(K,ℝ)) (hinj : Function.Injective lam)
    (xa xb : K) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (Cemetery (ProbabilityState K))) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityCemeteryMap lam) μ μ)
    (hmaximal : probabilityCemeteryAverage lam a b μ = (Real.log (rate a b) : EReal)) :
    μ = Measure.dirac (Sum.inl (balancedProbabilityState xa xb)) := by
  have hr := (probability_growth_continuous lam a ha (fun x => (hlam x).1)).measurable
  have hfinite : probabilityCemeteryAverage lam a b μ ≠ ⊥ := hmaximal.trans_ne (EReal.coe_ne_bot _)
  obtain ⟨hp,hf,he⟩ := extendedLogIntegral_finite_reduction _ (killedMultiplier_measurable _ hr)
    _ (probability_cemetery_log_upper lam a b ha hab.le hlam) μ hfinite
  let χ₀ := balancedProbabilityState xa xb
  let ν := cemeteryBaseMeasure χ₀ μ
  have hνT := cemetery_base_preserving (probabilityMap lam) (probabilityGrowth lam)
    (probability_map_measurable lam a ha (fun x => (hlam x).1)) χ₀ μ hT hp
  have hνr := cemetery_base_regular (probabilityGrowth lam) hr χ₀ μ hp
  have htransfer := cemetery_log_integrable_transfer (probabilityGrowth lam) hr χ₀ μ hp hf
  have hνmax : (∫ χ, Real.log (probabilityGrowth lam χ) ∂ν) = Real.log (rate a b) := by
    apply EReal.coe_injective
    rw [← htransfer.2,← he]
    exact hmaximal
  have hνeq := probability_state_unique_maximizer lam hinj xa xb a b ha hab hxa hxb hlam
    ν hνT hνr htransfer.1 hνmax
  rw [← cemetery_base_lift (probabilityGrowth lam) χ₀ μ hp]
  change ν.map Sum.inl = _
  rw [hνeq,Measure.map_dirac measurable_inl]

theorem probability_cemetery_balanced_invariant (lam : C(K,ℝ))
    (xa xb : K) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b)
    (hlam : ∀ x, a ≤ lam x) :
    MeasurePreserving (probabilityCemeteryMap lam)
      (Measure.dirac (Sum.inl (balancedProbabilityState xa xb)))
      (Measure.dirac (Sum.inl (balancedProbabilityState xa xb))) := by
  have hr := (probability_growth_continuous lam a ha hlam).measurable
  have hT := killedMap_measurable (probabilityMap lam) (probabilityGrowth lam)
    (probability_map_measurable lam a ha hlam) hr
  have hpos : 0 < probabilityGrowth lam (balancedProbabilityState xa xb) := by
    rw [balanced_probability_growth lam xa xb a b ha hab hxa hxb]
    exact rate_pos ha hab
  refine ⟨hT,?_⟩
  change (Measure.dirac _).map (killedMap _ _) = _
  rw [Measure.map_dirac hT]
  congr 1
  rw [killedMap_regular _ _ _ hpos,balanced_probability_fixed lam xa xb a b ha hab hxa hxb]

theorem probability_cemetery_balanced_average (lam : C(K,ℝ))
    (xa xb : K) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b) :
    probabilityCemeteryAverage lam a b (Measure.dirac (Sum.inl (balancedProbabilityState xa xb))) =
      (Real.log (rate a b) : EReal) := by
  have hr := (probability_growth_continuous lam a ha (fun x => (hlam x).1)).measurable
  have hg := balanced_probability_growth lam xa xb a b ha hab hxa hxb
  have hp : ∀ᵐ χ ∂Measure.dirac (Sum.inl (balancedProbabilityState xa xb)),
      0 < killedMultiplier (probabilityGrowth lam) χ := by
    rw [ae_dirac_eq]
    change 0 < probabilityGrowth lam (balancedProbabilityState xa xb)
    rw [hg]
    exact rate_pos ha hab
  have hf : Integrable (fun χ => Real.log (killedMultiplier (probabilityGrowth lam) χ))
      (Measure.dirac (Sum.inl (balancedProbabilityState xa xb))) :=
    (integrable_const _).congr (ae_eq_dirac _).symm
  rw [probabilityCemeteryAverage,extendedLogIntegral_of_integrable _ (killedMultiplier_measurable _ hr)
    _ (probability_cemetery_log_upper lam a b ha hab.le hlam) _ hp hf,integral_dirac]
  simp only [killedMultiplier,Sum.elim_inl,hg]

def probabilityCemeteryAverages (lam : C(K,ℝ)) (a b : ℝ) : Set EReal :=
  {v | ∃ μ : Measure (Cemetery (ProbabilityState K)), IsProbabilityMeasure μ ∧
    MeasurePreserving (probabilityCemeteryMap lam) μ μ ∧ probabilityCemeteryAverage lam a b μ = v}

/-- The maximal invariant average exists, equals the exact logarithmic rate,
and its unique invariant probability law is the balanced endpoint Dirac law. -/
theorem probability_cemetery_maximum (lam : C(K,ℝ)) (hinj : Function.Injective lam)
    (xa xb : K) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hxa : lam xa = a) (hxb : lam xb = b)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b) :
    IsGreatest (probabilityCemeteryAverages lam a b) (Real.log (rate a b) : EReal) ∧
      ∀ (μ : Measure (Cemetery (ProbabilityState K))) [IsProbabilityMeasure μ],
        MeasurePreserving (probabilityCemeteryMap lam) μ μ →
        (probabilityCemeteryAverage lam a b μ = (Real.log (rate a b) : EReal) ↔
          μ = Measure.dirac (Sum.inl (balancedProbabilityState xa xb))) := by
  constructor
  · constructor
    · exact ⟨Measure.dirac (Sum.inl (balancedProbabilityState xa xb)),inferInstance,
        probability_cemetery_balanced_invariant lam xa xb a b ha hab hxa hxb (fun x => (hlam x).1),
        probability_cemetery_balanced_average lam xa xb a b ha hab hxa hxb hlam⟩
    · rintro v ⟨μ,hμ,hT,rfl⟩
      letI : IsProbabilityMeasure μ := hμ
      exact probability_cemetery_invariant_bound lam a b ha hab hlam μ hT
  · intro μ _ hT
    constructor
    · exact probability_cemetery_unique_maximizer lam hinj xa xb a b ha hab hxa hxb hlam μ hT
    · intro hμ
      rw [hμ]
      exact probability_cemetery_balanced_average lam xa xb a b ha hab hxa hxb hlam

end BB
