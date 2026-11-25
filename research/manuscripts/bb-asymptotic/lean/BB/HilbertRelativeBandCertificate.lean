import BB.HilbertBandCertificate

/-!
# The exact common-support endpoint-band certificate

The ambient compact spectral set may be larger than the common support `S`.
The suprema below are taken over `S` intersected with the endpoint bands, and
the masses are evaluated in the original ambient probability measures. Thus
no implicit replacement of an ambient supremum by a relative one is made.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

def restrictedCoordinate (lam : C(K,ℝ)) (S : Set K) : C(S,ℝ) :=
  ⟨fun x => lam x,lam.continuous.comp continuous_subtype_val⟩

def relativeLowerBand (lam : C(K,ℝ)) (S : Set K) (a δ : ℝ) : Set K :=
  S ∩ lowerSpectralBand lam a δ
def relativeUpperBand (lam : C(K,ℝ)) (S : Set K) (b δ : ℝ) : Set K :=
  S ∩ upperSpectralBand lam b δ
def relativeBandGamma (lam : C(K,ℝ)) (S : Set K) (a b δ u : ℝ) : ℝ :=
  bandMultiplierSup lam (relativeLowerBand lam S a δ) u ^ leftWeight a b *
    bandMultiplierSup lam (relativeUpperBand lam S b δ) u ^ rightWeight a b
def relativeBandConstant (lam : C(K,ℝ)) (S : Set K) (a b δ : ℝ) : ℝ :=
  sSup (relativeBandGamma lam S a b δ '' Icc a b)

lemma relative_lower_band_isClosed (lam : C(K,ℝ)) (S : Set K) (hS : IsClosed S) (a δ : ℝ) :
    IsClosed (relativeLowerBand lam S a δ) := hS.inter (lower_spectral_band_isClosed lam a δ)
lemma relative_upper_band_isClosed (lam : C(K,ℝ)) (S : Set K) (hS : IsClosed S) (b δ : ℝ) :
    IsClosed (relativeUpperBand lam S b δ) := hS.inter (upper_spectral_band_isClosed lam b δ)

lemma relative_band_gamma_eq_subtype (lam : C(K,ℝ)) (S : Set K) [CompactSpace S] (a b δ u : ℝ) :
    relativeBandGamma lam S a b δ u = spectralBandGamma (restrictedCoordinate lam S) a b δ u := by
  have hL : multiplierModulus lam u '' relativeLowerBand lam S a δ =
      multiplierModulus (restrictedCoordinate lam S) u '' lowerSpectralBand (restrictedCoordinate lam S) a δ := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.1,⟨x.2,hx⟩,rfl⟩
  have hU : multiplierModulus lam u '' relativeUpperBand lam S b δ =
      multiplierModulus (restrictedCoordinate lam S) u '' upperSpectralBand (restrictedCoordinate lam S) b δ := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,hx.1⟩,hx.2,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.1,⟨x.2,hx⟩,rfl⟩
  unfold relativeBandGamma spectralBandGamma bandMultiplierSup
  rw [hL,hU]

lemma relative_band_constant_eq_subtype (lam : C(K,ℝ)) (S : Set K) [CompactSpace S] (a b δ : ℝ) :
    relativeBandConstant lam S a b δ = spectralBandConstant (restrictedCoordinate lam S) a b δ := by
  unfold relativeBandConstant spectralBandConstant
  simp_rw [relative_band_gamma_eq_subtype]

lemma relative_band_gamma_le_constant (lam : C(K,ℝ)) (S : Set K) (hS : IsCompact S)
    (a b δ u : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (xa xb : K) (hxaS : xa ∈ S) (hxbS : xb ∈ S) (hxa : lam xa = a) (hxb : lam xb = b)
    (hu : u ∈ Icc a b) : relativeBandGamma lam S a b δ u ≤ relativeBandConstant lam S a b δ := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [relative_band_gamma_eq_subtype,relative_band_constant_eq_subtype]
  exact spectral_band_gamma_le_constant (restrictedCoordinate lam S) a b δ u ha hab hδ
    ⟨xa,hxaS⟩ ⟨xb,hxbS⟩ hxa hxb hu

lemma relative_band_gamma_pos (lam : C(K,ℝ)) (S : Set K) (hS : IsCompact S)
    (a b δ u : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (xa xb : K) (hxaS : xa ∈ S) (hxbS : xb ∈ S) (hxa : lam xa = a) (hxb : lam xb = b)
    (hau : a < u) (hub : u < b) : 0 < relativeBandGamma lam S a b δ u := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  rw [relative_band_gamma_eq_subtype]
  exact spectral_band_gamma_pos (restrictedCoordinate lam S) a b δ u ha hab hδ.le
    ⟨xa,hxaS⟩ ⟨xb,hxbS⟩ hxa hxb hau hub

/-- The literal relative-band supremum limit from the manuscript. -/
theorem relative_band_constant_tendsto (lam : C(K,ℝ)) (S : Set K) (hS : IsCompact S)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (xa xb : K) (hxaS : xa ∈ S) (hxbS : xb ∈ S) (hxa : lam xa = a) (hxb : lam xb = b) :
    Tendsto (relativeBandConstant lam S a b) (𝓝[>] (0:ℝ)) (𝓝 (rate a b)) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  have heq : relativeBandConstant lam S a b = spectralBandConstant (restrictedCoordinate lam S) a b :=
    funext (fun δ => relative_band_constant_eq_subtype lam S a b δ)
  rw [heq]
  exact spectral_band_constant_tendsto (restrictedCoordinate lam S) a b ha hab
    ⟨xa,hxaS⟩ ⟨xb,hxbS⟩ hxa hxb

lemma continuous_band_integral_pos_at_support_ae (ν : ProbabilityMeasure K) (q : C(K,ℝ))
    (hq : ∀ x, 0 ≤ q x) (B V : Set K) (hV : IsOpen V)
    (hVB : ∀ᵐ y ∂(ν : Measure K), y ∈ V → y ∈ B)
    (x : K) (hx : x ∈ measureSupport (ν : Measure K)) (hxV : x ∈ V) (hqx : 0 < q x) :
    0 < ∫ y in B, q y ∂(ν : Measure K) := by
  let U : Set K := V ∩ {y | 0 < q y}
  have hU : IsOpen U := hV.inter (isOpen_lt continuous_const q.continuous)
  have hxU : x ∈ U := ⟨hxV,hqx⟩
  have hmass : 0 < (ν : Measure K) (Function.support q ∩ B) := by
    have hpos : 0 < (ν : Measure K) U := pos_iff_ne_zero.mpr (hx U hU hxU)
    apply hpos.trans_le (measure_mono_ae ?_)
    filter_upwards [hVB] with y hy
    intro hyU
    exact ⟨(show 0 < q y from hyU.2).ne',hy hyU.1⟩
  exact (setIntegral_pos_iff_support_of_nonneg_ae (eventually_of_forall hq)
    (continuous_integrable_probability ν q).restrict).mpr hmass

lemma probability_band_mass_pos_of_integral_pos (ν : ProbabilityMeasure K) (q : K → ℝ) (B : Set K)
    (hpos : 0 < ∫ x in B, q x ∂(ν : Measure K)) : 0 < probabilityBandMass ν B := by
  apply (probability_band_mass_pos_iff ν B).mpr
  intro hzero
  have hr := Measure.restrict_eq_zero.mpr hzero
  rw [hr,integral_zero_measure] at hpos
  exact lt_irrefl 0 hpos

lemma probability_mean_interior_of_endpoint_support_ae (lam : C(K,ℝ)) (ν : ProbabilityMeasure K)
    (a b : ℝ) (hab : a < b) (hlam : ∀ᵐ x ∂(ν : Measure K), a ≤ lam x ∧ lam x ≤ b)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b)
    (hsa : xa ∈ measureSupport (ν : Measure K)) (hsb : xb ∈ measureSupport (ν : Measure K)) :
    a < (∫ x, lam x ∂(ν : Measure K)) ∧ (∫ x, lam x ∂(ν : Measure K)) < b := by
  have hint := continuous_integrable_probability ν lam
  have hleft : 0 < ∫ x, lam x-a ∂(ν : Measure K) := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hlam.mono (fun _ hx => sub_nonneg.mpr hx.1)) (hint.sub (integrable_const a))).mpr
    have hpos : 0 < (ν : Measure K) {x | a < lam x} := pos_iff_ne_zero.mpr
      (hsb _ (isOpen_lt continuous_const lam.continuous) (by change a < lam xb; rw [hxb]; exact hab))
    apply hpos.trans_le (measure_mono ?_)
    intro x hx
    exact (sub_pos.mpr (show a < lam x from hx)).ne'
  have hright : 0 < ∫ x, b-lam x ∂(ν : Measure K) := by
    apply (integral_pos_iff_support_of_nonneg_ae
      (hlam.mono (fun _ hx => sub_nonneg.mpr hx.2)) ((integrable_const b).sub hint)).mpr
    have hpos : 0 < (ν : Measure K) {x | lam x < b} := pos_iff_ne_zero.mpr
      (hsa _ (isOpen_lt lam.continuous continuous_const) (by change lam xa < b; rw [hxa]; exact hab))
    apply hpos.trans_le (measure_mono ?_)
    intro x hx
    exact (sub_pos.mpr (show lam x < b from hx)).ne'
  rw [integral_sub hint (integrable_const a)] at hleft
  rw [integral_sub (integrable_const b) hint] at hright
  simp only [integral_const,measure_univ,ENNReal.one_toReal,one_smul] at hleft hright
  exact ⟨sub_pos.mp hleft,sub_pos.mp hright⟩

/-- The manuscript's exact common-support certificate, with all quantities
evaluated in the original ambient probability measures and suprema restricted
to the actual common support. -/
theorem probability_relative_band_certificate (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (S : Set K) (hS : IsClosed S) (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hlam : ∀ x ∈ S, a ≤ lam x ∧ lam x ≤ b)
    (xa xb : K) (hxaS : xa ∈ S) (hxbS : xb ∈ S) (hxa : lam xa = a) (hxb : lam xb = b)
    (hν : measureSupport (χ.1 : Measure K) = S) (hζ : measureSupport (χ.2 : Measure K) = S)
    (hR : 0 < probabilityGrowthSq lam χ) :
    Real.log (probabilityGrowth lam χ) ≤ Real.log (relativeBandGamma lam S a b δ (probabilityMean lam χ)) +
      probabilityBandPotential a b (relativeLowerBand lam S a δ) (relativeUpperBand lam S b δ) (probabilityMap lam χ).1 -
      probabilityBandPotential a b (relativeLowerBand lam S a δ) (relativeUpperBand lam S b δ) χ.1 := by
  let u := probabilityMean lam χ
  let L := relativeLowerBand lam S a δ
  let U := relativeUpperBand lam S b δ
  have hνfull : ∀ᵐ x ∂(χ.1 : Measure K), x ∈ S := by simpa only [hν] using ae_mem_measureSupport (χ.1 : Measure K)
  have hζfull : ∀ᵐ x ∂(χ.2 : Measure K), x ∈ S := by simpa only [hζ] using ae_mem_measureSupport (χ.2 : Measure K)
  have hνa : xa ∈ measureSupport (χ.1 : Measure K) := hν.symm ▸ hxaS
  have hνb : xb ∈ measureSupport (χ.1 : Measure K) := hν.symm ▸ hxbS
  have hζa : xa ∈ measureSupport (χ.2 : Measure K) := hζ.symm ▸ hxaS
  have hζb : xb ∈ measureSupport (χ.2 : Measure K) := hζ.symm ▸ hxbS
  obtain ⟨hau,hub⟩ := probability_mean_interior_of_endpoint_support_ae lam χ.2 a b hab
    (hζfull.mono (fun x hx => hlam x hx)) xa xb hxa hxb hζa hζb
  have hu : 0 < u := ha.trans hau
  have hL := relative_lower_band_isClosed lam S hS a δ
  have hU := relative_upper_band_isClosed lam S hS b δ
  have hxaL : xa ∈ L := ⟨hxaS,endpoint_mem_lower_band lam a δ hδ.le xa hxa⟩
  have hxbU : xb ∈ U := ⟨hxbS,endpoint_mem_upper_band lam b δ hδ.le xb hxb⟩
  have hLint : 0 < ∫ x in L, (1-lam x/u)^2 ∂(χ.1 : Measure K) := by
    have hVB : ∀ᵐ x ∂(χ.1 : Measure K), x ∈ {x | lam x < a+δ} → x ∈ L :=
      hνfull.mono (fun x hx hlt => ⟨hx,(hlam x hx).1,(show lam x < a+δ from hlt).le⟩)
    have hq : 0 < quadraticMultiplier lam u xa := by
      rw [quadraticMultiplier_apply,hxa]
      exact pow_pos (sub_pos.mpr ((div_lt_one hu).mpr hau)) 2
    simpa only [quadraticMultiplier_apply] using
      continuous_band_integral_pos_at_support_ae χ.1 (quadraticMultiplier lam u)
        (quadraticMultiplier_nonneg lam u) L {x | lam x < a+δ}
        (isOpen_lt lam.continuous continuous_const) hVB xa hνa
        (by change lam xa < a+δ; rw [hxa]; linarith) hq
  have hUint : 0 < ∫ x in U, (1-lam x/u)^2 ∂(χ.1 : Measure K) := by
    have hVB : ∀ᵐ x ∂(χ.1 : Measure K), x ∈ {x | b-δ < lam x} → x ∈ U :=
      hνfull.mono (fun x hx hlt => ⟨hx,(show b-δ < lam x from hlt).le,(hlam x hx).2⟩)
    have hq : 0 < quadraticMultiplier lam u xb := by
      rw [quadraticMultiplier_apply,hxb]
      exact sq_pos_of_ne_zero (sub_neg.mpr ((one_lt_div hu).mpr hub)).ne
    simpa only [quadraticMultiplier_apply] using
      continuous_band_integral_pos_at_support_ae χ.1 (quadraticMultiplier lam u)
        (quadraticMultiplier_nonneg lam u) U {x | b-δ < lam x}
        (isOpen_lt continuous_const lam.continuous) hVB xb hνb
        (by change b-δ < lam xb; rw [hxb]; linarith) hq
  have hs : 0 < bandMultiplierSup lam L u := by
    apply (abs_pos.mpr (sub_pos.mpr ((div_lt_one hu).mpr hau)).ne').trans_le
    simpa only [hxa] using multiplier_le_bandSup lam L hL.isCompact u xa hxaL
  have ht : 0 < bandMultiplierSup lam U u := by
    apply (abs_pos.mpr (sub_neg.mpr ((one_lt_div hu).mpr hub)).ne).trans_le
    simpa only [hxb] using multiplier_le_bandSup lam U hU.isCompact u xb hxbU
  have hbound := probability_band_transfer_bound lam χ a b ha hab hR L U hL.measurableSet hU.measurableSet
    (probability_band_mass_pos_of_integral_pos χ.1 _ L hLint)
    (probability_band_mass_pos_of_integral_pos χ.1 _ U hUint) hLint hUint _ _ hs ht
    (fun x hx => multiplier_le_bandSup lam L hL.isCompact u x hx)
    (fun x hx => multiplier_le_bandSup lam U hU.isCompact u x hx)
  have hlog : Real.log (relativeBandGamma lam S a b δ u) =
      leftWeight a b * Real.log (bandMultiplierSup lam L u) +
      rightWeight a b * Real.log (bandMultiplierSup lam U u) := by
    rw [relativeBandGamma,Real.log_mul (Real.rpow_pos_of_pos hs _).ne' (Real.rpow_pos_of_pos ht _).ne',
      Real.log_rpow hs,Real.log_rpow ht]
  rwa [← hlog] at hbound

theorem probability_relative_band_uniform (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (S : Set K) (hS : IsClosed S) (a b δ : ℝ) (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (hlam : ∀ x ∈ S, a ≤ lam x ∧ lam x ≤ b)
    (xa xb : K) (hxaS : xa ∈ S) (hxbS : xb ∈ S) (hxa : lam xa = a) (hxb : lam xb = b)
    (hν : measureSupport (χ.1 : Measure K) = S) (hζ : measureSupport (χ.2 : Measure K) = S)
    (hR : 0 < probabilityGrowthSq lam χ) :
    Real.log (probabilityGrowth lam χ) ≤ Real.log (relativeBandConstant lam S a b δ) +
      probabilityBandPotential a b (relativeLowerBand lam S a δ) (relativeUpperBand lam S b δ) (probabilityMap lam χ).1 -
      probabilityBandPotential a b (relativeLowerBand lam S a δ) (relativeUpperBand lam S b δ) χ.1 := by
  have hζfull : ∀ᵐ x ∂(χ.2 : Measure K), x ∈ S := by simpa only [hζ] using ae_mem_measureSupport (χ.2 : Measure K)
  obtain ⟨hau,hub⟩ := probability_mean_interior_of_endpoint_support_ae lam χ.2 a b hab
    (hζfull.mono (fun x hx => hlam x hx)) xa xb hxa hxb (hζ.symm ▸ hxaS) (hζ.symm ▸ hxbS)
  have hbound := probability_relative_band_certificate lam χ S hS a b δ ha hab hδ hlam xa xb hxaS hxbS hxa hxb hν hζ hR
  have hle := Real.log_le_log
    (relative_band_gamma_pos lam S hS.isCompact a b δ _ ha hab hδ xa xb hxaS hxbS hxa hxb hau hub)
    (relative_band_gamma_le_constant lam S hS.isCompact a b δ _ ha hab hδ xa xb hxaS hxbS hxa hxb ⟨hau.le,hub.le⟩)
  change Real.log (relativeBandGamma lam S a b δ (probabilityMean lam χ)) ≤
    Real.log (relativeBandConstant lam S a b δ) at hle
  linarith only [hbound,hle]

end BB
