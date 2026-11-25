import BB.EndpointBandSup
import BB.HilbertPersistentSupport

/-!
# Actual spectral-band mass transfer

The band masses below are evaluations of the actual probability measures.
Their update, conditional multiplier averages, positivity from support, and
the logarithmic transfer inequality are all proved from `withDensity`.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

def probabilityBandMass (ν : ProbabilityMeasure K) (B : Set K) : ℝ := ((ν : Measure K) B).toReal

lemma probability_band_mass_nonneg (ν : ProbabilityMeasure K) (B : Set K) :
    0 ≤ probabilityBandMass ν B := ENNReal.toReal_nonneg

lemma probability_band_mass_le_one (ν : ProbabilityMeasure K) (B : Set K) :
    probabilityBandMass ν B ≤ 1 := by
  have h := (ENNReal.toReal_le_toReal (measure_ne_top (ν : Measure K) B) ENNReal.one_ne_top).mpr
    (prob_le_one : (ν : Measure K) B ≤ 1)
  simpa only [ENNReal.one_toReal] using h

lemma probability_band_mass_pos_iff (ν : ProbabilityMeasure K) (B : Set K) :
    0 < probabilityBandMass ν B ↔ (ν : Measure K) B ≠ 0 := by
  constructor
  · intro h hz
    simp only [probabilityBandMass,hz,ENNReal.zero_toReal,lt_self_iff_false] at h
  · intro h
    exact ENNReal.toReal_pos h (measure_ne_top (ν : Measure K) B)

lemma probability_closed_mass_upperSemicontinuous (B : Set K) (hB : IsClosed B) :
    UpperSemicontinuous (fun ν : ProbabilityMeasure K => (ν : Measure K) B) := by
  apply upperSemicontinuous_iff_limsup_le.mpr
  intro ν
  exact ProbabilityMeasure.limsup_measure_closed_le_of_tendsto tendsto_id hB

lemma probability_closed_band_mass_measurable [MeasurableSpace (ProbabilityMeasure K)]
    [BorelSpace (ProbabilityMeasure K)] (B : Set K) (hB : IsClosed B) :
    Measurable (fun ν : ProbabilityMeasure K => probabilityBandMass ν B) :=
  ENNReal.measurable_toReal.comp (probability_closed_mass_upperSemicontinuous B hB).measurable

lemma probability_reweight_band_mass (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (hreg : 0 < ∫ x, q x ∂(ν : Measure K))
    (B : Set K) (hB : MeasurableSet B) :
    probabilityBandMass (probabilityReweight ν q hq hreg) B =
      (∫ x in B, q x ∂(ν : Measure K)) / (∫ x, q x ∂(ν : Measure K)) := by
  have hint : IntegrableOn q B (ν : Measure K) := (continuous_integrable_probability ν q).restrict
  have hnonneg : ∀ᵐ x ∂(ν : Measure K).restrict B, 0 ≤ q x := eventually_of_forall hq
  have hnum := (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm
  change (normalizedReweight (ν : Measure K) (fun x => ENNReal.ofReal (q x)) B).toReal = _
  rw [normalizedReweight_apply _ _ hB, continuous_density_mass ν q hq,hnum,
    ENNReal.toReal_mul,ENNReal.toReal_inv,ENNReal.toReal_ofReal hreg.le,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hnonneg)]
  ring

lemma continuous_band_integral_pos_at_support (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (B V : Set K) (hV : IsOpen V) (hVB : V ⊆ B)
    (x : K) (hx : x ∈ measureSupport (ν : Measure K)) (hxV : x ∈ V) (hqx : 0 < q x) :
    0 < ∫ y in B, q y ∂(ν : Measure K) := by
  let U : Set K := V ∩ {y | 0 < q y}
  have hU : IsOpen U := hV.inter (isOpen_lt continuous_const q.continuous)
  have hxU : x ∈ U := ⟨hxV,hqx⟩
  have hmass : 0 < (ν : Measure K) (Function.support q ∩ B) := by
    have hpos : 0 < (ν : Measure K) U := pos_iff_ne_zero.mpr (hx U hU hxU)
    apply hpos.trans_le (measure_mono ?_)
    intro y hy
    exact ⟨(show 0 < q y from hy.2).ne',hVB hy.1⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae (eventually_of_forall hq)
    (continuous_integrable_probability ν q).restrict).mpr hmass

lemma continuous_band_integral_le (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (B : Set K) (hB : MeasurableSet B) (C : ℝ) (hbound : ∀ x ∈ B, q x ≤ C) :
    (∫ x in B, q x ∂(ν : Measure K)) ≤ probabilityBandMass ν B * C := by
  have hle : q ≤ᵐ[(ν : Measure K).restrict B] (fun _ => C) :=
    (ae_restrict_mem hB).mono (fun x hx => hbound x hx)
  have h := integral_mono_ae (continuous_integrable_probability ν q).restrict
    (integrable_const C) hle
  simpa only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,probabilityBandMass] using h

def conditionalBandAverage (ν : ProbabilityMeasure K) (q : C(K,ℝ)) (B : Set K) : ℝ :=
  (∫ x in B, q x ∂(ν : Measure K)) / probabilityBandMass ν B

lemma conditional_band_average_pos (ν : ProbabilityMeasure K) (q : C(K,ℝ)) (B : Set K)
    (hmass : 0 < probabilityBandMass ν B) (hint : 0 < ∫ x in B, q x ∂(ν : Measure K)) :
    0 < conditionalBandAverage ν q B := div_pos hint hmass

lemma conditional_band_average_le (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (B : Set K) (hB : MeasurableSet B) (hmass : 0 < probabilityBandMass ν B)
    (C : ℝ) (hbound : ∀ x ∈ B, q x ≤ C) : conditionalBandAverage ν q B ≤ C := by
  apply (div_le_iff hmass).mpr
  simpa only [mul_comm] using continuous_band_integral_le ν q B hB C hbound

lemma probability_reweight_band_average (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (hreg : 0 < ∫ x, q x ∂(ν : Measure K))
    (B : Set K) (hB : MeasurableSet B) (hmass : 0 < probabilityBandMass ν B) :
    probabilityBandMass (probabilityReweight ν q hq hreg) B =
      probabilityBandMass ν B * conditionalBandAverage ν q B / (∫ x, q x ∂(ν : Measure K)) := by
  rw [probability_reweight_band_mass ν q hq hreg B hB]
  unfold conditionalBandAverage
  field_simp [hmass.ne']

def probabilityBandPotential (a b : ℝ) (L U : Set K) (ν : ProbabilityMeasure K) : ℝ :=
  bandPotential (leftWeight a b) (rightWeight a b) (probabilityBandMass ν L) (probabilityBandMass ν U)

lemma probability_band_potential_nonneg (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (L U : Set K) (ν : ProbabilityMeasure K) :
    0 ≤ probabilityBandPotential a b L U ν := by
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  have hl := Real.log_nonpos (probability_band_mass_nonneg ν L) (probability_band_mass_le_one ν L)
  have hu := Real.log_nonpos (probability_band_mass_nonneg ν U) (probability_band_mass_le_one ν U)
  unfold probabilityBandPotential bandPotential
  have hpl := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hp.le (by norm_num : (0:ℝ) ≤ 2)) hl
  have hqu := mul_nonpos_of_nonneg_of_nonpos (div_nonneg hq.le (by norm_num : (0:ℝ) ≤ 2)) hu
  linarith only [hpl,hqu]

/-- The exact measure-level logarithmic transfer estimate for two positive
bands, with any valid positive bounds on their multiplier moduli. -/
lemma probability_band_transfer_bound (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hR : 0 < probabilityGrowthSq lam χ)
    (L U : Set K) (hL : MeasurableSet L) (hU : MeasurableSet U)
    (hlmass : 0 < probabilityBandMass χ.1 L) (humass : 0 < probabilityBandMass χ.1 U)
    (hlint : 0 < ∫ x in L, (1-lam x/probabilityMean lam χ)^2 ∂(χ.1 : Measure K))
    (huint : 0 < ∫ x in U, (1-lam x/probabilityMean lam χ)^2 ∂(χ.1 : Measure K))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hls : ∀ x ∈ L, |1-lam x/probabilityMean lam χ| ≤ s)
    (hut : ∀ x ∈ U, |1-lam x/probabilityMean lam χ| ≤ t) :
    Real.log (probabilityGrowth lam χ) ≤ leftWeight a b * Real.log s + rightWeight a b * Real.log t +
      probabilityBandPotential a b L U (probabilityMap lam χ).1 - probabilityBandPotential a b L U χ.1 := by
  let q := quadraticMultiplier lam (probabilityMean lam χ)
  have hreg : 0 < ∫ x, q x ∂(χ.1 : Measure K) := by
    simpa only [q,quadraticMultiplier_apply,probabilityGrowthSq] using hR
  have hLA := conditional_band_average_pos χ.1 q L hlmass
    (by simpa only [q,quadraticMultiplier_apply] using hlint)
  have hUA := conditional_band_average_pos χ.1 q U humass
    (by simpa only [q,quadraticMultiplier_apply] using huint)
  have hLs : conditionalBandAverage χ.1 q L ≤ s^2 :=
    conditional_band_average_le χ.1 q L hL hlmass (s^2) (fun x hx => by
      simp only [q,quadraticMultiplier_apply]
      exact (sq_abs (1-lam x/probabilityMean lam χ)) ▸
        pow_le_pow_left (abs_nonneg _) (hls x hx) 2)
  have hUt : conditionalBandAverage χ.1 q U ≤ t^2 :=
    conditional_band_average_le χ.1 q U hU humass (t^2) (fun x hx => by
      simp only [q,quadraticMultiplier_apply]
      exact (sq_abs (1-lam x/probabilityMean lam χ)) ▸
        pow_le_pow_left (abs_nonneg _) (hut x hx) 2)
  have hmapL : probabilityBandMass (probabilityMap lam χ).1 L = probabilityBandMass χ.1 L *
      conditionalBandAverage χ.1 q L / probabilityGrowthSq lam χ := by
    rw [probabilityMap,dif_pos hR]
    simpa only [q,quadraticMultiplier_apply,probabilityGrowthSq] using
      probability_reweight_band_average χ.1 q (quadraticMultiplier_nonneg lam _) hreg L hL hlmass
  have hmapU : probabilityBandMass (probabilityMap lam χ).1 U = probabilityBandMass χ.1 U *
      conditionalBandAverage χ.1 q U / probabilityGrowthSq lam χ := by
    rw [probabilityMap,dif_pos hR]
    simpa only [q,quadraticMultiplier_apply,probabilityGrowthSq] using
      probability_reweight_band_average χ.1 q (quadraticMultiplier_nonneg lam _) hreg U hU humass
  have hlog : Real.log (probabilityGrowth lam χ) = Real.log (probabilityGrowthSq lam χ) / 2 := by
    exact Real.log_sqrt hR.le
  rw [hlog]
  unfold probabilityBandPotential
  rw [hmapL,hmapU]
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  exact band_transfer_bound _ _ _ _ _ _ _ _ _ (endpoint_weights_sum (by linarith)) hp.le hq.le
    hlmass humass hLA hUA hR hs ht hLs hUt

lemma probability_band_integral_pos_of_next_mass (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (hR : 0 < probabilityGrowthSq lam χ) (B : Set K) (hB : MeasurableSet B)
    (hnext : 0 < probabilityBandMass (probabilityMap lam χ).1 B) :
    0 < ∫ x in B, (1-lam x/probabilityMean lam χ)^2 ∂(χ.1 : Measure K) := by
  rw [probabilityMap,dif_pos hR] at hnext
  rw [probability_reweight_band_mass χ.1 _ _ _ B hB] at hnext
  simp only [quadraticMultiplier_apply] at hnext
  have h := (lt_div_iff hR).mp hnext
  simpa only [zero_mul] using h

/-- An exact full-band transfer bound requiring only current and next band
mass positivity; atoms and a common support are unnecessary. -/
lemma probability_exact_band_transfer_bound (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b) (hR : 0 < probabilityGrowthSq lam χ)
    (hlmass : 0 < probabilityBandMass χ.1 (lowerSpectralBand lam a δ))
    (humass : 0 < probabilityBandMass χ.1 (upperSpectralBand lam b δ))
    (hlnext : 0 < probabilityBandMass (probabilityMap lam χ).1 (lowerSpectralBand lam a δ))
    (hunext : 0 < probabilityBandMass (probabilityMap lam χ).1 (upperSpectralBand lam b δ)) :
    Real.log (probabilityGrowth lam χ) ≤ exactBandLog a b δ (probabilityMean lam χ) +
      probabilityBandPotential a b (lowerSpectralBand lam a δ) (upperSpectralBand lam b δ) (probabilityMap lam χ).1 -
      probabilityBandPotential a b (lowerSpectralBand lam a δ) (upperSpectralBand lam b δ) χ.1 := by
  have hu : 0 < probabilityMean lam χ := ha.trans_le
    (functional_mean_lower lam a (fun x => (hlam x).1) (probabilityStateEmbedding χ))
  have hL := (lower_spectral_band_isClosed lam a δ).measurableSet
  have hU := (upper_spectral_band_isClosed lam b δ).measurableSet
  exact probability_band_transfer_bound lam χ a b ha hab hR _ _ hL hU hlmass humass
    (probability_band_integral_pos_of_next_mass lam χ hR _ hL hlnext)
    (probability_band_integral_pos_of_next_mass lam χ hR _ hU hunext)
    _ _ (lowerBandFactor_pos hδ hu) (upperBandFactor_pos hδ hu)
    (fun _ hx => lower_band_factor_bound hu hx.1 hx.2)
    (fun _ hx => upper_band_factor_bound hu hx.1 hx.2)

lemma probability_mean_interior_of_endpoint_support (lam : C(K,ℝ)) (ν : ProbabilityMeasure K)
    (a b : ℝ) (hab : a < b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b)
    (hsa : xa ∈ measureSupport (ν : Measure K)) (hsb : xb ∈ measureSupport (ν : Measure K)) :
    a < (∫ x, lam x ∂(ν : Measure K)) ∧ (∫ x, lam x ∂(ν : Measure K)) < b := by
  let ql : C(K,ℝ) := lam - ContinuousMap.const K a
  let qu : C(K,ℝ) := ContinuousMap.const K b - lam
  have hl := continuous_band_integral_pos_at_support ν ql
    (fun x => sub_nonneg.mpr (hlam x).1) univ univ isOpen_univ (subset_refl _) xb hsb (mem_univ _)
    (by change 0 < lam xb-a; rw [hxb]; exact sub_pos.mpr hab)
  have hu := continuous_band_integral_pos_at_support ν qu
    (fun x => sub_nonneg.mpr (hlam x).2) univ univ isOpen_univ (subset_refl _) xa hsa (mem_univ _)
    (by change 0 < b-lam xa; rw [hxa]; exact sub_pos.mpr hab)
  simp only [integral_univ,ql,qu,ContinuousMap.sub_apply,ContinuousMap.const_apply] at hl hu
  rw [integral_sub (continuous_integrable_probability ν lam) (integrable_const a)] at hl
  rw [integral_sub (integrable_const b) (continuous_integrable_probability ν lam)] at hu
  simp only [integral_const,measure_univ,ENNReal.one_toReal,one_smul] at hl hu
  exact ⟨sub_pos.mp hl,sub_pos.mp hu⟩

lemma lower_band_mass_pos_of_support (lam : C(K,ℝ)) (ν : ProbabilityMeasure K)
    (a δ : ℝ) (hδ : 0 < δ) (hlam : ∀ x, a ≤ lam x)
    (xa : K) (hxa : lam xa = a) (hsa : xa ∈ measureSupport (ν : Measure K)) :
    0 < probabilityBandMass ν (lowerSpectralBand lam a δ) := by
  apply (probability_band_mass_pos_iff ν _).mpr
  let V : Set K := {x | lam x < a+δ}
  have hV : IsOpen V := isOpen_lt lam.continuous continuous_const
  have hxV : xa ∈ V := by change lam xa < a+δ; rw [hxa]; linarith
  have hVB : V ⊆ lowerSpectralBand lam a δ := fun x hx => ⟨hlam x,(show lam x < a+δ from hx).le⟩
  exact fun hz => hsa V hV hxV (measure_mono_null hVB hz)

lemma upper_band_mass_pos_of_support (lam : C(K,ℝ)) (ν : ProbabilityMeasure K)
    (b δ : ℝ) (hδ : 0 < δ) (hlam : ∀ x, lam x ≤ b)
    (xb : K) (hxb : lam xb = b) (hsb : xb ∈ measureSupport (ν : Measure K)) :
    0 < probabilityBandMass ν (upperSpectralBand lam b δ) := by
  apply (probability_band_mass_pos_iff ν _).mpr
  let V : Set K := {x | b-δ < lam x}
  have hV : IsOpen V := isOpen_lt continuous_const lam.continuous
  have hxV : xb ∈ V := by change b-δ < lam xb; rw [hxb]; linarith
  have hVB : V ⊆ upperSpectralBand lam b δ := fun x hx => ⟨(show b-δ < lam x from hx).le,hlam x⟩
  exact fun hz => hsb V hV hxV (measure_mono_null hVB hz)

lemma lower_band_multiplier_integral_pos_of_support (lam : C(K,ℝ)) (ν : ProbabilityMeasure K)
    (a δ u : ℝ) (ha : 0 < a) (hδ : 0 < δ) (hau : a < u) (hlam : ∀ x, a ≤ lam x)
    (xa : K) (hxa : lam xa = a) (hsa : xa ∈ measureSupport (ν : Measure K)) :
    0 < ∫ x in lowerSpectralBand lam a δ, (1-lam x/u)^2 ∂(ν : Measure K) := by
  have hu : 0 < u := ha.trans hau
  have hqpos : 0 < quadraticMultiplier lam u xa := by
    rw [quadraticMultiplier_apply,hxa]
    exact pow_pos (sub_pos.mpr ((div_lt_one hu).mpr hau)) 2
  have h := continuous_band_integral_pos_at_support ν (quadraticMultiplier lam u)
    (quadraticMultiplier_nonneg lam u) (lowerSpectralBand lam a δ) {x | lam x < a+δ}
    (isOpen_lt lam.continuous continuous_const) (fun x hx => ⟨hlam x,(show lam x < a+δ from hx).le⟩)
    xa hsa (by change lam xa < a+δ; rw [hxa]; linarith) hqpos
  simpa only [quadraticMultiplier_apply] using h

lemma upper_band_multiplier_integral_pos_of_support (lam : C(K,ℝ)) (ν : ProbabilityMeasure K)
    (b δ u : ℝ) (hu : 0 < u) (hδ : 0 < δ) (hub : u < b) (hlam : ∀ x, lam x ≤ b)
    (xb : K) (hxb : lam xb = b) (hsb : xb ∈ measureSupport (ν : Measure K)) :
    0 < ∫ x in upperSpectralBand lam b δ, (1-lam x/u)^2 ∂(ν : Measure K) := by
  have hqpos : 0 < quadraticMultiplier lam u xb := by
    rw [quadraticMultiplier_apply,hxb]
    apply sq_pos_of_ne_zero
    exact (sub_neg.mpr ((one_lt_div hu).mpr hub)).ne
  have h := continuous_band_integral_pos_at_support ν (quadraticMultiplier lam u)
    (quadraticMultiplier_nonneg lam u) (upperSpectralBand lam b δ) {x | b-δ < lam x}
    (isOpen_lt continuous_const lam.continuous) (fun x hx => ⟨(show b-δ < lam x from hx).le,hlam x⟩)
    xb hsb (by change b-δ < lam xb; rw [hxb]; linarith) hqpos
  simpa only [quadraticMultiplier_apply] using h

/-- The genuine supremum band certificate on any compact spectral domain
whose two endpoint points lie in both consecutive supports. No endpoint atoms
or integrability of the logarithmic transfer function are assumed. -/
theorem probability_hilbert_band_certificate (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b)
    (hνa : xa ∈ measureSupport (χ.1 : Measure K)) (hνb : xb ∈ measureSupport (χ.1 : Measure K))
    (hζa : xa ∈ measureSupport (χ.2 : Measure K)) (hζb : xb ∈ measureSupport (χ.2 : Measure K))
    (hR : 0 < probabilityGrowthSq lam χ) :
    Real.log (probabilityGrowth lam χ) ≤ Real.log (spectralBandGamma lam a b δ (probabilityMean lam χ)) +
      probabilityBandPotential a b (lowerSpectralBand lam a δ) (upperSpectralBand lam b δ) (probabilityMap lam χ).1 -
      probabilityBandPotential a b (lowerSpectralBand lam a δ) (upperSpectralBand lam b δ) χ.1 := by
  let u := probabilityMean lam χ
  obtain ⟨hau,hub⟩ := probability_mean_interior_of_endpoint_support lam χ.2 a b hab hlam xa xb hxa hxb hζa hζb
  have hu : 0 < u := ha.trans hau
  have hL := lower_spectral_band_isClosed lam a δ
  have hU := upper_spectral_band_isClosed lam b δ
  have hxaL := endpoint_mem_lower_band lam a δ hδ.le xa hxa
  have hxbU := endpoint_mem_upper_band lam b δ hδ.le xb hxb
  have hs : 0 < bandMultiplierSup lam (lowerSpectralBand lam a δ) u := by
    apply (abs_pos.mpr (sub_pos.mpr ((div_lt_one hu).mpr hau)).ne').trans_le
    simpa only [hxa] using multiplier_le_bandSup lam _ hL.isCompact u xa hxaL
  have ht : 0 < bandMultiplierSup lam (upperSpectralBand lam b δ) u := by
    apply (abs_pos.mpr (sub_neg.mpr ((one_lt_div hu).mpr hub)).ne).trans_le
    simpa only [hxb] using multiplier_le_bandSup lam _ hU.isCompact u xb hxbU
  have hbound := probability_band_transfer_bound lam χ a b ha hab hR _ _ hL.measurableSet hU.measurableSet
    (lower_band_mass_pos_of_support lam χ.1 a δ hδ (fun x => (hlam x).1) xa hxa hνa)
    (upper_band_mass_pos_of_support lam χ.1 b δ hδ (fun x => (hlam x).2) xb hxb hνb)
    (lower_band_multiplier_integral_pos_of_support lam χ.1 a δ u ha hδ hau (fun x => (hlam x).1) xa hxa hνa)
    (upper_band_multiplier_integral_pos_of_support lam χ.1 b δ u hu hδ hub (fun x => (hlam x).2) xb hxb hνb)
    _ _ hs ht
    (fun x hx => multiplier_le_bandSup lam _ hL.isCompact u x hx)
    (fun x hx => multiplier_le_bandSup lam _ hU.isCompact u x hx)
  have hlog : Real.log (spectralBandGamma lam a b δ u) =
      leftWeight a b * Real.log (bandMultiplierSup lam (lowerSpectralBand lam a δ) u) +
      rightWeight a b * Real.log (bandMultiplierSup lam (upperSpectralBand lam b δ) u) := by
    rw [spectralBandGamma,Real.log_mul (Real.rpow_pos_of_pos hs _).ne' (Real.rpow_pos_of_pos ht _).ne',
      Real.log_rpow hs,Real.log_rpow ht]
  rwa [← hlog] at hbound

theorem probability_hilbert_band_uniform (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b)
    (hνa : xa ∈ measureSupport (χ.1 : Measure K)) (hνb : xb ∈ measureSupport (χ.1 : Measure K))
    (hζa : xa ∈ measureSupport (χ.2 : Measure K)) (hζb : xb ∈ measureSupport (χ.2 : Measure K))
    (hR : 0 < probabilityGrowthSq lam χ) :
    Real.log (probabilityGrowth lam χ) ≤ Real.log (spectralBandConstant lam a b δ) +
      probabilityBandPotential a b (lowerSpectralBand lam a δ) (upperSpectralBand lam b δ) (probabilityMap lam χ).1 -
      probabilityBandPotential a b (lowerSpectralBand lam a δ) (upperSpectralBand lam b δ) χ.1 := by
  obtain ⟨hau,hub⟩ := probability_mean_interior_of_endpoint_support lam χ.2 a b hab hlam xa xb hxa hxb hζa hζb
  have hbound := probability_hilbert_band_certificate lam χ a b δ ha hab hδ hlam xa xb hxa hxb hνa hνb hζa hζb hR
  have hle := Real.log_le_log (spectral_band_gamma_pos lam a b δ _ ha hab hδ.le xa xb hxa hxb hau hub)
    (spectral_band_gamma_le_constant lam a b δ _ ha hab hδ xa xb hxa hxb ⟨hau.le,hub.le⟩)
  change Real.log (spectralBandGamma lam a b δ (probabilityMean lam χ)) ≤
    Real.log (spectralBandConstant lam a b δ) at hle
  linarith only [hbound,hle]

end BB
