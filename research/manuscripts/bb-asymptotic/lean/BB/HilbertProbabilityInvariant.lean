import BB.HilbertProbability
import BB.LogCocycleInvariant

/-!
# Semiuniform bounds and invariant averages on probability-measure states

These are statements on the manuscript's actual probability-measure state
space, with the library weak topology and an isolated terminal state. The
proof embeds into the independently proved compact positive-functional
model. The invariant inequality uses a genuine extended logarithmic integral;
no integrability or ergodicity hypothesis is required.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology BigOperators
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K]

lemma probability_mean_continuous (lam : C(K,ℝ)) : Continuous (probabilityMean lam) := by
  have h := (functional_mean_continuous lam).comp probability_state_embedding_continuous
  simpa only [Function.comp_def,probability_mean_embedding] using h

lemma probability_growth_bound (lam : C(K,ℝ)) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b) (χ : ProbabilityState K) :
    probabilityGrowth lam χ ≤ 1+b/a := by
  rw [← probability_growth_embedding]
  exact functional_growth_bound lam a b ha hab hlam _

lemma probability_prefix_continuous (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b) (n : ℕ) :
    Continuous (prefixProduct (probabilityGrowth lam) (probabilityMap lam) n) := by
  have h := (functional_prefix_continuous lam a b ha hab hlam n).comp probability_state_embedding_continuous
  simpa only [Function.comp_def,probability_prefix_embedding] using h

/-- A proved uniform envelope on the actual weak probability-measure states. -/
lemma probability_prefix_envelope (lam : C(K,ℝ)) (a b γ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (hγ : rate a b < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (χ : ProbabilityState K),
      prefixProduct (probabilityGrowth lam) (probabilityMap lam) n χ ≤ C*γ^n := by
  obtain ⟨C,hC,henv⟩ := compact_coordinate_functional_envelope lam a b γ ha hab hlam hγ
  refine ⟨C,hC,?_⟩
  intro n χ
  simpa only [probability_prefix_embedding] using henv n (probabilityStateEmbedding χ)

lemma probability_killed_prefix_envelope (lam : C(K,ℝ)) (a b γ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (hγ : rate a b < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (χ : Cemetery (ProbabilityState K)),
      prefixProduct (killedMultiplier (probabilityGrowth lam))
        (killedMap (probabilityMap lam) (probabilityGrowth lam)) n χ ≤ C*γ^n := by
  apply killed_all_prefix_envelopes (probabilityMap lam) (probabilityGrowth lam)
    (probability_growth_nonneg lam) (rate a b)
    (div_nonneg (sub_nonneg.mpr hab) (by linarith))
    (fun γ hγ => probability_prefix_envelope lam a b γ ha hab hlam hγ) γ hγ

/-- The original Hilbert semiuniform inequality, on every actual nonterminal
segment of the isolated-terminal probability-measure state map. -/
theorem probability_hilbert_semiuniform (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (η : ℝ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ n (χ : Cemetery (ProbabilityState K)),
      (∀ j < n, 0 < killedMultiplier (probabilityGrowth lam)
        ((killedMap (probabilityMap lam) (probabilityGrowth lam))^[j] χ)) →
      (∑ j in Finset.range n, Real.log (killedMultiplier (probabilityGrowth lam)
        ((killedMap (probabilityMap lam) (probabilityGrowth lam))^[j] χ))) ≤
        (n:ℝ)*(Real.log (rate a b)+η)+B := by
  apply semiuniform_log_sum_of_all_envelopes _ _ (rate a b) (rate_pos ha hab)
    (fun γ hγ => probability_killed_prefix_envelope lam a b γ ha hab.le hlam hγ) η hη

section Invariant
variable [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

lemma probability_map_measurable (lam : C(K,ℝ)) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ x, a ≤ lam x) : Measurable (probabilityMap lam) := by
  classical
  let S : Set (ProbabilityState K) := {χ | 0 < probabilityGrowthSq lam χ}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (probability_growth_sq_continuous lam a ha hlam)).measurableSet
  apply measurable_of_restrict_of_restrict_compl hS
  · apply Continuous.measurable
    apply ContinuousOn.restrict
    intro χ hχ
    exact (probability_map_continuousAt_regular lam a ha hlam χ
      (ne_of_gt (Real.sqrt_pos.mpr hχ))).continuousWithinAt
  · have heq : Sᶜ.restrict (probabilityMap lam) = Subtype.val := by
      funext χ
      exact dif_neg χ.2
    rw [heq]
    exact measurable_subtype_coe

/-- Every invariant probability measure satisfies the sharp extended-average
bound. Terminal mass and nonintegrable negative parts are included. -/
theorem probability_hilbert_invariant_bound (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (Cemetery (ProbabilityState K))) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (killedMap (probabilityMap lam) (probabilityGrowth lam)) μ μ) :
    extendedLogIntegral (killedMultiplier (probabilityGrowth lam)) (Real.log (1+b/a)) μ ≤
      (Real.log (rate a b) : EReal) := by
  have hr : Measurable (killedMultiplier (probabilityGrowth lam)) :=
    killedMultiplier_measurable _ (probability_growth_continuous lam a ha (fun x => (hlam x).1)).measurable
  have hu : ∀ χ : Cemetery (ProbabilityState K),
      0 < killedMultiplier (probabilityGrowth lam) χ →
      Real.log (killedMultiplier (probabilityGrowth lam) χ) ≤ Real.log (1+b/a) := by
    intro χ hχ
    cases χ with
    | inl χ => exact Real.log_le_log hχ (probability_growth_bound lam a b ha hab.le hlam χ)
    | inr u => exact (lt_irrefl 0 hχ).elim
  exact invariant_extended_log_le_of_all_envelopes μ _ hT _ hr _ hu (rate a b) (rate_pos ha hab)
    (fun γ hγ => probability_killed_prefix_envelope lam a b γ ha hab.le hlam hγ)

end Invariant
end BB
