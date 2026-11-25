import BB.ExactBandScalar
import BB.HilbertProbability

/-!
# The manuscript's endpoint-band suprema

These are genuine suprema over the spectral bands. Compactness proves their
boundedness, and the exact scalar certificate implies that the optimal band
constant is already equal to the sharp endpoint rate for all sufficiently
small positive widths.
-/

noncomputable section
namespace BB
open Set Filter
open scoped Topology
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def multiplierModulus (lam : C(K,ℝ)) (u : ℝ) : C(K,ℝ) :=
  ⟨fun x => |1-lam x/u|, (continuous_const.sub (lam.continuous.div_const u)).abs⟩

def bandMultiplierSup (lam : C(K,ℝ)) (B : Set K) (u : ℝ) : ℝ :=
  sSup (multiplierModulus lam u '' B)

lemma band_multiplier_bddAbove (lam : C(K,ℝ)) (B : Set K) (hB : IsCompact B) (u : ℝ) :
    BddAbove (multiplierModulus lam u '' B) :=
  (hB.image (multiplierModulus lam u).continuous).bddAbove

lemma multiplier_le_bandSup (lam : C(K,ℝ)) (B : Set K) (hB : IsCompact B) (u : ℝ)
    (x : K) (hx : x ∈ B) : |1-lam x/u| ≤ bandMultiplierSup lam B u :=
  le_csSup (band_multiplier_bddAbove lam B hB u) ⟨x,hx,rfl⟩

lemma bandSup_le (lam : C(K,ℝ)) (B : Set K) (hB : B.Nonempty) (u C : ℝ)
    (hbound : ∀ x ∈ B, |1-lam x/u| ≤ C) : bandMultiplierSup lam B u ≤ C := by
  apply csSup_le (hB.image (multiplierModulus lam u))
  rintro _ ⟨x,hx,rfl⟩
  exact hbound x hx

lemma bandSup_nonneg (lam : C(K,ℝ)) (B : Set K) (hB : IsCompact B) (hBne : B.Nonempty) (u : ℝ) :
    0 ≤ bandMultiplierSup lam B u := by
  obtain ⟨x,hx⟩ := hBne
  exact (abs_nonneg _).trans (multiplier_le_bandSup lam B hB u x hx)

def lowerSpectralBand (lam : C(K,ℝ)) (a δ : ℝ) : Set K := lam ⁻¹' Icc a (a+δ)
def upperSpectralBand (lam : C(K,ℝ)) (b δ : ℝ) : Set K := lam ⁻¹' Icc (b-δ) b

lemma lower_spectral_band_isClosed (lam : C(K,ℝ)) (a δ : ℝ) :
    IsClosed (lowerSpectralBand lam a δ) := isClosed_Icc.preimage lam.continuous
lemma upper_spectral_band_isClosed (lam : C(K,ℝ)) (b δ : ℝ) :
    IsClosed (upperSpectralBand lam b δ) := isClosed_Icc.preimage lam.continuous

def spectralBandGamma (lam : C(K,ℝ)) (a b δ u : ℝ) : ℝ :=
  bandMultiplierSup lam (lowerSpectralBand lam a δ) u ^ leftWeight a b *
    bandMultiplierSup lam (upperSpectralBand lam b δ) u ^ rightWeight a b

def spectralBandConstant (lam : C(K,ℝ)) (a b δ : ℝ) : ℝ :=
  sSup (spectralBandGamma lam a b δ '' Icc a b)

lemma endpoint_mem_lower_band (lam : C(K,ℝ)) (a δ : ℝ) (hδ : 0 ≤ δ)
    (x : K) (hx : lam x = a) : x ∈ lowerSpectralBand lam a δ := by
  change a ≤ lam x ∧ lam x ≤ a+δ
  rw [hx]
  exact ⟨le_rfl,by linarith⟩

lemma endpoint_mem_upper_band (lam : C(K,ℝ)) (b δ : ℝ) (hδ : 0 ≤ δ)
    (x : K) (hx : lam x = b) : x ∈ upperSpectralBand lam b δ := by
  change b-δ ≤ lam x ∧ lam x ≤ b
  rw [hx]
  exact ⟨by linarith,le_rfl⟩

lemma spectral_band_gamma_sandwich (lam : C(K,ℝ)) (a b δ u : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 ≤ δ)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b) (hu : u ∈ Icc a b) :
    endpointProduct a b u ≤ spectralBandGamma lam a b δ u ∧
      spectralBandGamma lam a b δ u ≤ exactBandProduct a b δ u := by
  have hu0 : 0 < u := ha.trans_le hu.1
  have hL := (lower_spectral_band_isClosed lam a δ).isCompact
  have hU := (upper_spectral_band_isClosed lam b δ).isCompact
  have haL := endpoint_mem_lower_band lam a δ hδ xa hxa
  have hbU := endpoint_mem_upper_band lam b δ hδ xb hxb
  have hL0 := bandSup_nonneg lam _ hL ⟨xa,haL⟩ u
  have hU0 := bandSup_nonneg lam _ hU ⟨xb,hbU⟩ u
  have hLa : (u-a)/u ≤ bandMultiplierSup lam (lowerSpectralBand lam a δ) u := by
    have h := multiplier_le_bandSup lam _ hL u xa haL
    rw [hxa, ← div_self hu0.ne', ← sub_div, abs_div,abs_of_pos hu0,
      abs_of_nonneg (sub_nonneg.mpr hu.1)] at h
    exact h
  have hUb : (b-u)/u ≤ bandMultiplierSup lam (upperSpectralBand lam b δ) u := by
    have h := multiplier_le_bandSup lam _ hU u xb hbU
    rw [hxb, ← div_self hu0.ne', ← sub_div, abs_div,abs_of_pos hu0,
      abs_of_nonpos (sub_nonpos.mpr hu.2)] at h
    simpa only [neg_sub] using h
  have hLf := bandSup_le lam _ ⟨xa,haL⟩ u (lowerBandFactor a δ u)
    (fun x hx => lower_band_factor_bound hu0 hx.1 hx.2)
  have hUf := bandSup_le lam _ ⟨xb,hbU⟩ u (upperBandFactor b δ u)
    (fun x hx => upper_band_factor_bound hu0 hx.1 hx.2)
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  constructor
  · exact mul_le_mul
      (Real.rpow_le_rpow (div_nonneg (sub_nonneg.mpr hu.1) hu0.le) hLa hp.le)
      (Real.rpow_le_rpow (div_nonneg (sub_nonneg.mpr hu.2) hu0.le) hUb hq.le)
      (Real.rpow_nonneg (div_nonneg (sub_nonneg.mpr hu.2) hu0.le) _)
      (Real.rpow_nonneg hL0 _)
  · exact mul_le_mul (Real.rpow_le_rpow hL0 hLf hp.le)
      (Real.rpow_le_rpow hU0 hUf hq.le) (Real.rpow_nonneg hU0 _)
      (Real.rpow_nonneg (hL0.trans hLf) _)

lemma spectral_band_gamma_pos (lam : C(K,ℝ)) (a b δ u : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 ≤ δ)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b)
    (hau : a < u) (hub : u < b) : 0 < spectralBandGamma lam a b δ u := by
  have hprod : 0 < endpointProduct a b u := by
    exact mul_pos (Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hau) (ha.trans hau)) _)
      (Real.rpow_pos_of_pos (div_pos (sub_pos.mpr hub) (ha.trans hau)) _)
  exact hprod.trans_le (spectral_band_gamma_sandwich lam a b δ u ha hab hδ xa xb hxa hxb ⟨hau.le,hub.le⟩).1

lemma spectral_band_gamma_bddAbove (lam : C(K,ℝ)) (a b δ : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b) :
    BddAbove (spectralBandGamma lam a b δ '' Icc a b) := by
  obtain ⟨C,hC⟩ := (isCompact_Icc.image_of_continuousOn
    (exact_band_product_continuousOn a b δ ha hδ)).bddAbove
  refine ⟨C,?_⟩
  rintro _ ⟨u,hu,rfl⟩
  exact (spectral_band_gamma_sandwich lam a b δ u ha hab hδ.le xa xb hxa hxb hu).2.trans
    (hC ⟨u,hu,rfl⟩)

lemma spectral_band_gamma_le_constant (lam : C(K,ℝ)) (a b δ u : ℝ)
    (ha : 0 < a) (hab : a < b) (hδ : 0 < δ)
    (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b) (hu : u ∈ Icc a b) :
    spectralBandGamma lam a b δ u ≤ spectralBandConstant lam a b δ :=
  le_csSup (spectral_band_gamma_bddAbove lam a b δ ha hab hδ xa xb hxa hxb) ⟨u,hu,rfl⟩

/-- For every spectral set containing both endpoints, its genuine band
supremum is exactly the sharp rate once the bands are sufficiently narrow.
The width may be chosen using only the two endpoints. -/
theorem spectral_band_constant_eventually_exact (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (b-a)/2 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      spectralBandConstant lam a b ε = rate a b ∧
      ∀ u ∈ Icc a b, spectralBandGamma lam a b ε u ≤ rate a b ∧
        (spectralBandGamma lam a b ε u = rate a b ↔ u = (a+b)/2) := by
  obtain ⟨δ,hδ,hδd,hcert⟩ := exists_exact_endpoint_band a b ha hab
  refine ⟨δ,hδ,hδd,?_⟩
  intro ε hε hεδ
  have hmean : (a+b)/2 ∈ Icc a b := ⟨by linarith,by linarith⟩
  have hall : ∀ u ∈ Icc a b, spectralBandGamma lam a b ε u ≤ rate a b ∧
      (spectralBandGamma lam a b ε u = rate a b ↔ u = (a+b)/2) := by
    intro u hu
    have hs := spectral_band_gamma_sandwich lam a b ε u ha hab hε.le xa xb hxa hxb hu
    have hmono := exact_band_product_mono_width ha hab hεδ hu
    have hle := hs.2.trans (hmono.trans (hcert u hu).1)
    refine ⟨hle,⟨?_,?_⟩⟩
    · intro heq
      apply (hcert u hu).2.mp
      exact le_antisymm (hcert u hu).1 (heq ▸ hs.2.trans hmono)
    · intro heq
      have hp := (endpoint_product_eq_iff ha hab hu).mpr heq
      exact le_antisymm hle (hp ▸ hs.1)
  refine ⟨le_antisymm ?_ ?_,hall⟩
  · apply csSup_le (Set.Nonempty.image _ ⟨(a+b)/2,hmean⟩)
    rintro _ ⟨u,hu,rfl⟩
    exact (hall u hu).1
  · rw [← (hall ((a+b)/2) hmean).2.mpr rfl]
    exact spectral_band_gamma_le_constant lam a b ε ((a+b)/2) ha hab hε xa xb hxa hxb hmean

/-- The manuscript's one-sided endpoint-band constant limit, with the genuine
suprema and no atomic-endpoint assumption. -/
theorem spectral_band_constant_tendsto (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (xa xb : K) (hxa : lam xa = a) (hxb : lam xb = b) :
    Tendsto (spectralBandConstant lam a b) (𝓝[>] (0:ℝ)) (𝓝 (rate a b)) := by
  obtain ⟨δ,hδ,_hδd,hcert⟩ := spectral_band_constant_eventually_exact lam a b ha hab xa xb hxa hxb
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ)] with ε hε hεδ
  exact (hcert ε hε (le_of_lt hεδ)).1.symm

end BB
