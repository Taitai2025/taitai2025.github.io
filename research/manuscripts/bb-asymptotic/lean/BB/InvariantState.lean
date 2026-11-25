import BB.InvariantPartition
import BB.SpectralTopology

/-!
# Invariant measures on the actual finite spectral state space

The abstract observable results from `InvariantPartition` are instantiated
with the genuine two-simplex state and its total BB map.  The balanced
endpoint state is constructed and its invariant Dirac measure realizes the
sharp logarithmic average.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace BB

variable {ι : Type*} [Fintype ι]

instance simplexBorelSpace : BorelSpace (Simplex ι) :=
  Subtype.borelSpace {w : ι → ℝ | IsSimplex w}

theorem spectral_map_measurable (lam : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) : Measurable (spectralMap lam) := by
  classical
  let S : Set (SpectralState ι) := {χ | 0 < stateGrowthSq lam χ}
  have hS : MeasurableSet S :=
    (isOpen_lt continuous_const (state_growth_sq_continuous lam a ha hlam)).measurableSet
  apply measurable_of_restrict_of_restrict_compl hS
  · apply Continuous.measurable
    apply ContinuousOn.restrict
    intro χ hχ
    exact (spectral_map_continuousAt_regular lam a ha hlam χ
      (ne_of_gt (Real.sqrt_pos.mpr hχ))).continuousWithinAt
  · have heq : Sᶜ.restrict (spectralMap lam) = Subtype.val := by
      funext χ
      exact dif_neg χ.2
    rw [heq]
    exact measurable_subtype_coe

theorem balancedEndpointWeights_simplex (lo hi : ι) (hne : lo ≠ hi) :
    IsSimplex (balancedEndpointWeights lo hi) := by
  classical
  constructor
  · intro i
    unfold balancedEndpointWeights
    split_ifs <;> norm_num
  · rw [Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
      (fun i _ hn => by simp only [balancedEndpointWeights, hn.1, hn.2, or_self, if_false])]
    simp only [balancedEndpointWeights, true_or, or_true, if_true]
    norm_num

def balancedSpectralState (lo hi : ι) (hne : lo ≠ hi) : SpectralState ι :=
  (⟨balancedEndpointWeights lo hi, balancedEndpointWeights_simplex lo hi hne⟩,
   ⟨balancedEndpointWeights lo hi, balancedEndpointWeights_simplex lo hi hne⟩)

theorem balanced_mean (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi) :
    mean lam (balancedEndpointWeights lo hi) = (lam lo + lam hi) / 2 := by
  classical
  unfold mean
  rw [Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
    (fun i _ hn => by
      simp only [balancedEndpointWeights, hn.1, hn.2, or_self, if_false, mul_zero])]
  simp only [balancedEndpointWeights, true_or, or_true, if_true]
  ring

theorem balanced_growth_sq (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (ha : 0 < lam lo) (hab : lam lo < lam hi) :
    stateGrowthSq lam (balancedSpectralState lo hi hne) = (rate (lam lo) (lam hi))^2 := by
  classical
  change growthSq lam (balancedEndpointWeights lo hi) (balancedEndpointWeights lo hi) = _
  unfold growthSq
  rw [balanced_mean lam lo hi hne]
  rw [Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
    (fun i _ hn => by
      simp only [balancedEndpointWeights, hn.1, hn.2, or_self, if_false, mul_zero])]
  simp only [balancedEndpointWeights, true_or, or_true, if_true]
  rw [(midpoint_spectral_multiplier_eq_iff lam lo (lam lo) (lam hi) ha hab).mpr (Or.inl rfl),
    (midpoint_spectral_multiplier_eq_iff lam hi (lam lo) (lam hi) ha hab).mpr (Or.inr rfl)]
  ring

theorem balanced_growth (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (ha : 0 < lam lo) (hab : lam lo < lam hi) :
    stateGrowth lam (balancedSpectralState lo hi hne) = rate (lam lo) (lam hi) := by
  unfold stateGrowth
  rw [balanced_growth_sq lam lo hi hne ha hab, Real.sqrt_sq (rate_pos ha hab).le]

theorem balanced_spectral_fixed (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (ha : 0 < lam lo) (hab : lam lo < lam hi) :
    spectralMap lam (balancedSpectralState lo hi hne) = balancedSpectralState lo hi hne := by
  classical
  have hR : 0 < stateGrowthSq lam (balancedSpectralState lo hi hne) := by
    rw [balanced_growth_sq lam lo hi hne ha hab]
    exact sq_pos_of_pos (rate_pos ha hab)
  apply Prod.ext
  · apply Subtype.ext
    rw [(spectral_map_regular lam _ hR).1]
    change weightUpdate lam (balancedEndpointWeights lo hi) (balancedEndpointWeights lo hi) = _
    funext i
    change weightUpdate lam (balancedEndpointWeights lo hi) (balancedEndpointWeights lo hi) i =
      balancedEndpointWeights lo hi i
    unfold weightUpdate
    have hR' : growthSq lam (balancedEndpointWeights lo hi) (balancedEndpointWeights lo hi) =
        (rate (lam lo) (lam hi))^2 := balanced_growth_sq lam lo hi hne ha hab
    rw [balanced_mean lam lo hi hne, hR']
    by_cases hilo : i = lo
    · subst i
      rw [(midpoint_spectral_multiplier_eq_iff lam lo (lam lo) (lam hi) ha hab).mpr (Or.inl rfl)]
      exact mul_div_cancel_left₀ _ (ne_of_gt (sq_pos_of_pos (rate_pos ha hab)))
    · by_cases hihi : i = hi
      · subst i
        rw [(midpoint_spectral_multiplier_eq_iff lam hi (lam lo) (lam hi) ha hab).mpr (Or.inr rfl)]
        exact mul_div_cancel_left₀ _ (ne_of_gt (sq_pos_of_pos (rate_pos ha hab)))
      · simp only [balancedEndpointWeights, hilo, hihi, or_self, if_false, mul_zero, zero_div]
  · exact (spectral_map_regular lam _ hR).2

theorem balanced_dirac_invariant (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (a : ℝ) (ha : 0 < a) (hlam : ∀ i, a ≤ lam i) (hab : lam lo < lam hi) :
    MeasurePreserving (spectralMap lam)
      (Measure.dirac (balancedSpectralState lo hi hne))
      (Measure.dirac (balancedSpectralState lo hi hne)) := by
  have hm := spectral_map_measurable lam a ha hlam
  refine ⟨hm, ?_⟩
  rw [Measure.map_dirac hm, balanced_spectral_fixed lam lo hi hne (ha.trans_le (hlam lo)) hab]

theorem balanced_dirac_log_integral (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (ha : 0 < lam lo) (hab : lam lo < lam hi) :
    (∫ χ, Real.log (stateGrowth lam χ) ∂Measure.dirac (balancedSpectralState lo hi hne)) =
      Real.log (rate (lam lo) (lam hi)) := by
  rw [integral_dirac, balanced_growth lam lo hi hne ha hab]

theorem spectral_state_invariant_bound
    (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (μ : Measure (SpectralState ι)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (spectralMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < stateGrowthSq lam χ)
    (hf : Integrable (fun χ => Real.log (stateGrowth lam χ)) μ) :
    (∫ χ, Real.log (stateGrowth lam χ) ∂μ) ≤ Real.log (rate a b) := by
  apply finite_spectral_invariant_bound μ (spectralMap lam) hT lam a b ha hlam
    (fun χ => χ.1.1) (fun χ => χ.2.1) (fun χ => χ.1.2) (fun χ => χ.2.2)
    (fun i => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).measurable)
    (fun i => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).measurable)
    hregular _ _ hf
  · filter_upwards [hregular] with χ hχ
    exact (spectral_map_regular lam χ hχ).1
  · filter_upwards [hregular] with χ hχ
    exact congrArg Subtype.val (spectral_map_regular lam χ hχ).2

/-- On the actual product-of-simplexes state space, the invariant maximizing
measure itself is the balanced endpoint Dirac measure. -/
theorem spectral_state_unique_maximizer
    (lam : ι → ℝ) (hinj : Function.Injective lam) (lo hi : ι) (hne : lo ≠ hi)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (μ : Measure (SpectralState ι)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (spectralMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < stateGrowthSq lam χ)
    (hf : Integrable (fun χ => Real.log (stateGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (stateGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    μ = Measure.dirac (balancedSpectralState lo hi hne) := by
  have hupdate : ∀ᵐ χ ∂μ, (spectralMap lam χ).1.1 = weightUpdate lam χ.1.1 χ.2.1 := by
    filter_upwards [hregular] with χ hχ
    exact (spectral_map_regular lam χ hχ).1
  have hshift : ∀ᵐ χ ∂μ, (spectralMap lam χ).2.1 = χ.1.1 := by
    filter_upwards [hregular] with χ hχ
    exact congrArg Subtype.val (spectral_map_regular lam χ hχ).2
  have hstate := finite_spectral_maximal_state μ (spectralMap lam) hT lam hinj lo hi a b
    ha hab hlo hhi hlam (fun χ => χ.1.1) (fun χ => χ.2.1)
    (fun χ => χ.1.2) (fun χ => χ.2.2)
    (fun i => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).measurable)
    (fun i => ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).measurable)
    hregular hupdate hshift hf hmaximal
  have heq : (fun χ : SpectralState ι => χ) =ᵐ[μ] (fun _ => balancedSpectralState lo hi hne) := by
    filter_upwards [hstate] with χ hχ
    apply Prod.ext <;> apply Subtype.ext
    · exact eq_balancedEndpointWeights hχ.1.1 hχ.1.2
        (fun i hnlo hnhi => (hχ.2.2 i hnlo hnhi).1)
    · exact eq_balancedEndpointWeights hχ.2.1.1 hχ.2.1.2
        (fun i hnlo hnhi => (hχ.2.2 i hnlo hnhi).2)
  calc
    μ = μ.map (fun χ => χ) := Measure.map_id'.symm
    _ = μ.map (fun _ => balancedSpectralState lo hi hne) := Measure.map_congr heq
    _ = Measure.dirac (balancedSpectralState lo hi hne) := by
      rw [Measure.map_const, measure_univ, one_smul]

end BB
