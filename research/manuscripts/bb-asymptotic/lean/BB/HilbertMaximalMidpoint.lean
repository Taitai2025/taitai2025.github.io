import BB.HilbertMaximalBands

/-!
# Midpoint rigidity of every maximal invariant probability law

One sufficiently narrow endpoint band gives a nonnegative measurable defect.
The proved unbounded-coboundary Fatou argument forces the defect to vanish.
Band masses and the transfer function are not assumed bounded away from zero
or integrable, and the invariant law need not be ergodic.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

lemma probability_first_band_mass_measurable (B : Set K) (hB : IsClosed B) :
    Measurable (fun χ : ProbabilityState K => probabilityBandMass χ.1 B) :=
  ENNReal.measurable_toReal.comp
    ((probability_closed_mass_upperSemicontinuous B hB).comp_continuous continuous_fst).measurable

lemma probability_band_potential_measurable (a b : ℝ) (L U : Set K)
    (hL : IsClosed L) (hU : IsClosed U) :
    Measurable (fun χ : ProbabilityState K => probabilityBandPotential a b L U χ.1) :=
  (measurable_const.mul (probability_first_band_mass_measurable L hL).log).sub
    (measurable_const.mul (probability_first_band_mass_measurable U hU).log)

lemma probability_exact_band_log_measurable (lam : C(K,ℝ)) (a b δ : ℝ) :
    Measurable (fun χ : ProbabilityState K => exactBandLog a b δ (probabilityMean lam χ)) := by
  have hm := (probability_mean_continuous lam).measurable
  have hL : Measurable (fun χ : ProbabilityState K => lowerBandFactor a δ (probabilityMean lam χ)) :=
    ((hm.sub measurable_const).max (measurable_const.sub hm)).div hm
  have hU : Measurable (fun χ : ProbabilityState K => upperBandFactor b δ (probabilityMean lam χ)) :=
    ((measurable_const.sub hm).max ((hm.sub measurable_const).add measurable_const)).div hm
  exact (measurable_const.mul hL.log).add (measurable_const.mul hU.log)

/-- The midpoint conclusion holds for every maximal invariant law, without
passing to ergodic components. -/
theorem probability_maximal_midpoint (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (ProbabilityState K)) [IsProbabilityMeasure μ]
    (hT : MeasurePreserving (probabilityMap lam) μ μ)
    (hregular : ∀ᵐ χ ∂μ, 0 < probabilityGrowth lam χ)
    (hf : Integrable (fun χ => Real.log (probabilityGrowth lam χ)) μ)
    (hmaximal : (∫ χ, Real.log (probabilityGrowth lam χ) ∂μ) = Real.log (rate a b)) :
    ∀ᵐ χ ∂μ, probabilityMean lam χ = (a+b)/2 := by
  obtain ⟨δ,hδ,hδd,hcert⟩ := exists_exact_endpoint_band a b ha hab
  let L := lowerSpectralBand lam a δ
  let U := upperSpectralBand lam b δ
  let H : ProbabilityState K → ℝ := fun χ => probabilityBandPotential a b L U χ.1
  let D : ProbabilityState K → ℝ := fun χ => max
    (Real.log (rate a b) - exactBandLog a b δ (probabilityMean lam χ)) 0
  have hH : Measurable H := probability_band_potential_measurable a b L U
    (lower_spectral_band_isClosed lam a δ) (upper_spectral_band_isClosed lam b δ)
  have hHnonneg : ∀ χ, 0 ≤ H χ := fun χ => probability_band_potential_nonneg a b ha hab L U χ.1
  have hD : Measurable D := (measurable_const.sub (probability_exact_band_log_measurable lam a b δ)).max measurable_const
  have hDnonneg : ∀ χ, 0 ≤ D χ := fun _ => le_max_right _ _
  have hmean : ∀ χ : ProbabilityState K, probabilityMean lam χ ∈ Icc a b := fun χ =>
    ⟨functional_mean_lower lam a (fun x => (hlam x).1) (probabilityStateEmbedding χ),
      functional_mean_upper lam b (fun x => (hlam x).2) (probabilityStateEmbedding χ)⟩
  have hlogle : ∀ χ : ProbabilityState K, exactBandLog a b δ (probabilityMean lam χ) ≤ Real.log (rate a b) := by
    intro χ
    rw [exact_band_log_eq_log_product hδ (ha.trans_le (hmean χ).1)]
    exact Real.log_le_log (exactBandProduct_pos hδ (ha.trans_le (hmean χ).1)) (hcert _ (hmean χ)).1
  have hDeq : ∀ χ : ProbabilityState K, D χ = Real.log (rate a b) - exactBandLog a b δ (probabilityMean lam χ) :=
    fun χ => max_eq_left (sub_nonneg.mpr (hlogle χ))
  have hmass := probability_maximal_endpoint_bands_positive lam a b δ ha hab hδ (by linarith)
    hlam μ hT hregular hf hmaximal
  have hmassT := hT.quasiMeasurePreserving.ae hmass
  have hbound : ∀ᵐ χ ∂μ, Real.log (probabilityGrowth lam χ) + D χ ≤
      Real.log (rate a b) + H (probabilityMap lam χ) - H χ := by
    filter_upwards [hregular,hmass,hmassT] with χ hr hm hmT
    have h := probability_exact_band_transfer_bound lam χ a b δ ha hab hδ hlam (Real.sqrt_pos.mp hr)
      hm.1 hm.2 hmT.1 hmT.2
    rw [hDeq χ]
    change Real.log (probabilityGrowth lam χ) +
      (Real.log (rate a b)-exactBandLog a b δ (probabilityMean lam χ)) ≤
      Real.log (rate a b) + probabilityBandPotential a b L U (probabilityMap lam χ).1 -
        probabilityBandPotential a b L U χ.1
    exact (by linarith only [h])
  have hzero := coboundary_defect_zero_of_maximal_integral μ (probabilityMap lam) hT H hH hHnonneg
    _ hf (Real.log (rate a b)) D hD hDnonneg hbound hmaximal
  filter_upwards [hzero] with χ hχ
  rw [hDeq χ,sub_eq_zero] at hχ
  have hprod : exactBandProduct a b δ (probabilityMean lam χ) = rate a b := by
    apply Real.log_injOn_pos (show 0 < exactBandProduct a b δ (probabilityMean lam χ) from
      exactBandProduct_pos hδ (ha.trans_le (hmean χ).1)) (rate_pos ha hab)
    rw [← exact_band_log_eq_log_product hδ (ha.trans_le (hmean χ).1)]
    exact hχ.symm
  exact (hcert _ (hmean χ)).2.mp hprod

end BB
