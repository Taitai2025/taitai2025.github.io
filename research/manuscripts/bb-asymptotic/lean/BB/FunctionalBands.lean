import BB.FunctionalDynamics
import BB.Faces
import BB.SpectralLyapunov
import BB.BandScalar

/-!
# Finite continuous-band faces of the compact functional BB state

The faces are defined by zero masses of a finite continuous partition of
unity.  They are genuinely compact and invariant.  No atomic support
assumption is imposed on the underlying positive functionals.
-/

noncomputable section

open Set
open scoped BigOperators Topology

namespace BB

variable {K ι : Type*} [TopologicalSpace K] [CompactSpace K] [Fintype ι] [DecidableEq ι]

def bandWeights (φ : ι → C(K, ℝ)) (L : PositiveState K) (i : ι) : ℝ := L.1 (φ i)

theorem band_weights_simplex (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (hsum : ∑ i, φ i = 1) (L : PositiveState K) :
    IsSimplex (bandWeights φ L) :=
  ⟨fun i => L.2.1 (φ i) (hpos i), positive_unit_sum_one L φ hsum⟩

theorem band_weights_continuous (φ : ι → C(K, ℝ)) : Continuous (bandWeights φ) := by
  apply continuous_pi
  intro i
  exact positive_state_eval_continuous (φ i)

def InBandFace (φ : ι → C(K, ℝ)) (I : Finset ι) (χ : FunctionalState K) : Prop :=
  SupportedOn I (bandWeights φ χ.1) ∧ SupportedOn I (bandWeights φ χ.2)

abbrev BandFace (φ : ι → C(K, ℝ)) (I : Finset ι) :=
  {χ : FunctionalState K // InBandFace φ I χ}

theorem band_face_isClosed (φ : ι → C(K, ℝ)) (I : Finset ι) :
    IsClosed {χ : FunctionalState K | InBandFace φ I χ} := by
  classical
  exact ((supportedOn_isClosed I).preimage
    ((band_weights_continuous φ).comp continuous_fst)).inter
    ((supportedOn_isClosed I).preimage ((band_weights_continuous φ).comp continuous_snd))

instance bandFaceCompactSpace (φ : ι → C(K, ℝ)) (I : Finset ι) :
    CompactSpace (BandFace φ I) :=
  isCompact_iff_compactSpace.mp (band_face_isClosed φ I).isCompact

theorem functional_map_preserves_band_face (lam : C(K, ℝ)) (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (I : Finset ι) (χ : FunctionalState K)
    (hχ : InBandFace φ I χ) : InBandFace φ I (functionalMap lam χ) := by
  by_cases hR : 0 < functionalGrowthSq lam χ
  · obtain ⟨hfirst, hsecond⟩ := functional_map_regular lam χ hR
    constructor
    · intro i hi
      change (functionalMap lam χ).1.1 (φ i) = 0
      rw [hfirst]
      exact positive_reweight_zero_test χ.1 _ (φ i)
        (quadraticMultiplier_nonneg lam _) hR (hpos i) (hχ.1 i hi)
    · rw [hsecond]
      exact hχ.1
  · simpa only [functionalMap, dif_neg hR] using hχ

def bandFaceMap (lam : C(K, ℝ)) (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (I : Finset ι) (χ : BandFace φ I) : BandFace φ I :=
  ⟨functionalMap lam χ.1, functional_map_preserves_band_face lam φ hpos I χ.1 χ.2⟩

def bandFacePrefix (lam : C(K, ℝ)) (φ : ι → C(K, ℝ)) (I : Finset ι)
    (n : ℕ) (χ : BandFace φ I) : ℝ :=
  prefixProduct (functionalGrowth lam) (functionalMap lam) n χ.1

theorem band_face_iterate_val (lam : C(K, ℝ)) (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (I : Finset ι) (n : ℕ) (χ : BandFace φ I) :
    ((bandFaceMap lam φ hpos I)^[n] χ).1 = (functionalMap lam)^[n] χ.1 := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem band_face_prefix_cocycle (lam : C(K, ℝ)) (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (I : Finset ι) (n m : ℕ) (χ : BandFace φ I) :
    bandFacePrefix lam φ I (n+m) χ = bandFacePrefix lam φ I n χ *
      bandFacePrefix lam φ I m ((bandFaceMap lam φ hpos I)^[n] χ) := by
  unfold bandFacePrefix
  rw [prefix_product_cocycle, band_face_iterate_val]

theorem band_face_prefix_eq_product (lam : C(K, ℝ)) (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (I : Finset ι) (n : ℕ) (χ : BandFace φ I) :
    bandFacePrefix lam φ I n χ =
      prefixProduct (fun y : BandFace φ I => functionalGrowth lam y.1)
        (bandFaceMap lam φ hpos I) n χ := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
    change functionalGrowth lam χ.1 * bandFacePrefix lam φ I n (bandFaceMap lam φ hpos I χ) = _
    rw [ih]
    rfl

theorem functional_regular_image_in_band_support (lam : C(K, ℝ))
    (φ : ι → C(K, ℝ)) (hpos : ∀ i x, 0 ≤ φ i x) (hsum : ∑ i, φ i = 1)
    (χ : FunctionalState K) (hR : 0 < functionalGrowthSq lam χ) :
    InBandFace φ (positiveSupport (bandWeights φ χ.1)) (functionalMap lam χ) := by
  classical
  obtain ⟨hfirst, hsecond⟩ := functional_map_regular lam χ hR
  have hsupp := supported_positiveSupport (band_weights_simplex φ hpos hsum χ.1)
  constructor
  · intro i hi
    change (functionalMap lam χ).1.1 (φ i) = 0
    rw [hfirst]
    exact positive_reweight_zero_test χ.1 _ (φ i)
      (quadraticMultiplier_nonneg lam _) hR (hpos i) (hsupp i hi)
  · rw [hsecond]
    exact hsupp

/-- Bounds on the mean use only bands with nonzero mass. -/
theorem functional_mean_lower_on_bands (L : PositiveState K) (lam : C(K, ℝ))
    (φ : ι → C(K, ℝ)) (hpos : ∀ i x, 0 ≤ φ i x) (hsum : ∑ i, φ i = 1)
    (I : Finset ι) (hsupp : SupportedOn I (bandWeights φ L)) (a : ℝ)
    (hlam : ∀ i ∈ I, ∀ x, φ i x ≠ 0 → a ≤ lam x) : a ≤ L.1 lam := by
  classical
  calc
    a = ∑ i, a * L.1 (φ i) := by
      rw [← Finset.mul_sum, positive_unit_sum_one L φ hsum, mul_one]
    _ ≤ ∑ i, L.1 (lam * φ i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ I
      · have hle : L.1 (a • φ i) ≤ L.1 (lam * φ i) := by
          apply positive_unit_mono L.2
          intro x
          by_cases hx : φ i x = 0
          · simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul, hx, mul_zero, le_refl]
          · exact mul_le_mul_of_nonneg_right (hlam i hi x hx) (hpos i x)
        simpa only [_root_.map_smul, smul_eq_mul] using hle
      · have hz : L.1 (φ i) = 0 := hsupp i hi
        rw [positive_unit_zero_mul L lam (φ i) (hpos i) hz, hz, mul_zero]
    _ = L.1 lam := by rw [← map_sum, ← Finset.mul_sum, hsum, mul_one]

theorem functional_mean_upper_on_bands (L : PositiveState K) (lam : C(K, ℝ))
    (φ : ι → C(K, ℝ)) (hpos : ∀ i x, 0 ≤ φ i x) (hsum : ∑ i, φ i = 1)
    (I : Finset ι) (hsupp : SupportedOn I (bandWeights φ L)) (b : ℝ)
    (hlam : ∀ i ∈ I, ∀ x, φ i x ≠ 0 → lam x ≤ b) : L.1 lam ≤ b := by
  classical
  calc
    L.1 lam = ∑ i, L.1 (lam * φ i) := by rw [← map_sum, ← Finset.mul_sum, hsum, mul_one]
    _ ≤ ∑ i, b * L.1 (φ i) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ I
      · have hle : L.1 (lam * φ i) ≤ L.1 (b • φ i) := by
          apply positive_unit_mono L.2
          intro x
          by_cases hx : φ i x = 0
          · simp only [ContinuousMap.smul_apply, ContinuousMap.mul_apply, smul_eq_mul, hx, mul_zero, le_refl]
          · exact mul_le_mul_of_nonneg_right (hlam i hi x hx) (hpos i x)
        simpa only [_root_.map_smul, smul_eq_mul] using hle
      · have hz : L.1 (φ i) = 0 := hsupp i hi
        rw [positive_unit_zero_mul L lam (φ i) (hpos i) hz, hz, mul_zero]
    _ = b := by rw [← Finset.mul_sum, positive_unit_sum_one L φ hsum, mul_one]

def bandLyapunov (φ : ι → C(K, ℝ)) (a b : ℝ) (lo hi : ι) (χ : FunctionalState K) : ℝ :=
  endpointLyapunov a b lo hi (bandWeights φ χ.1)

theorem band_lyapunov_nonneg (φ : ι → C(K, ℝ)) (hpos : ∀ i x, 0 ≤ φ i x)
    (a b : ℝ) (lo hi : ι) (χ : FunctionalState K) : 0 ≤ bandLyapunov φ a b lo hi χ :=
  endpointLyapunov_nonneg (χ.1.2.1 (φ lo) (hpos lo)) (χ.1.2.1 (φ hi) (hpos hi))

theorem band_lyapunov_continuous (φ : ι → C(K, ℝ)) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (lo hi : ι) : Continuous (bandLyapunov φ a b lo hi) :=
  (endpointLyapunov_continuous ha hab lo hi).comp
    ((band_weights_continuous φ).comp continuous_fst)

theorem band_lyapunov_eq_zero_iff (φ : ι → C(K, ℝ)) (hpos : ∀ i x, 0 ≤ φ i x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (lo hi : ι) (χ : FunctionalState K) :
    bandLyapunov φ a b lo hi χ = 0 ↔ χ.1.1 (φ lo) = 0 ∨ χ.1.1 (φ hi) = 0 :=
  endpointLyapunov_eq_zero_iff ha hab lo hi _
    (χ.1.2.1 (φ lo) (hpos lo)) (χ.1.2.1 (φ hi) (hpos hi))

/-- A bounded multiplier on the support of a continuous band gives the same
bound for its normalized updated band mass. -/
theorem functional_reweight_band_bound (L : PositiveState K) (lam f : C(K, ℝ))
    (u s : ℝ) (hf : ∀ x, 0 ≤ f x)
    (hbound : ∀ x, f x ≠ 0 → |1-lam x/u| ≤ s)
    (hR : 0 < L.1 (quadraticMultiplier lam u)) :
    (positiveReweight L (quadraticMultiplier lam u) (quadraticMultiplier_nonneg lam u) hR).1 f ≤
      s^2 * L.1 f / L.1 (quadraticMultiplier lam u) := by
  rw [positiveReweight_apply]
  apply (div_le_div_right hR).mpr
  have hle : L.1 (quadraticMultiplier lam u * f) ≤ L.1 (s^2 • f) := by
    apply positive_unit_mono L.2
    intro x
    by_cases hx : f x = 0
    · simp only [ContinuousMap.mul_apply, ContinuousMap.smul_apply, smul_eq_mul, hx, mul_zero, le_refl]
    · have hq : quadraticMultiplier lam u x ≤ s^2 := by
        rw [quadraticMultiplier_apply]
        exact (sq_abs (1-lam x/u)).symm.le.trans
          (pow_le_pow_left (abs_nonneg _) (hbound x hx) 2)
      exact mul_le_mul_of_nonneg_right hq (hf x)
  simpa only [_root_.map_smul, smul_eq_mul] using hle

/-- Continuous endpoint-band masses give a one-step Lyapunov inequality for
the genuine functional update, including terminal states. -/
theorem functional_band_lyapunov_step (lam : C(K, ℝ)) (φ : ι → C(K, ℝ))
    (hpos : ∀ i x, 0 ≤ φ i x) (lo hi : ι) (A a b δ ρ : ℝ)
    (hA : 0 < A) (hAa : A ≤ a) (hab : a < b) (hδ : 0 ≤ δ)
    (χ : FunctionalState K)
    (hmean : a ≤ functionalMean lam χ ∧ functionalMean lam χ ≤ b)
    (hlo : ∀ x, φ lo x ≠ 0 → a ≤ lam x ∧ lam x ≤ a+δ)
    (hhi : ∀ x, φ hi x ≠ 0 → b-δ ≤ lam x ∧ lam x ≤ b)
    (hscalar : bandEndpointProduct A a b (functionalMean lam χ) δ ≤ ρ) :
    functionalGrowth lam χ ^ 2 * bandLyapunov φ a b lo hi (functionalMap lam χ) ≤
      ρ^2 * bandLyapunov φ a b lo hi χ := by
  rw [functional_growth_sq_identity]
  have ha : 0 < a := hA.trans_le hAa
  have hV := band_lyapunov_nonneg φ hpos a b lo hi χ
  by_cases hR : 0 < functionalGrowthSq lam χ
  · let u := functionalMean lam χ
    let s : ℝ := (u-a)/u + δ/A
    let t : ℝ := (b-u)/u + δ/A
    let p : ℝ := leftWeight a b
    let q : ℝ := rightWeight a b
    have hu : 0 < u := ha.trans_le hmean.1
    have hs : 0 ≤ s := add_nonneg (div_nonneg (sub_nonneg.mpr hmean.1) hu.le)
      (div_nonneg hδ hA.le)
    have ht : 0 ≤ t := add_nonneg (div_nonneg (sub_nonneg.mpr hmean.2) hu.le)
      (div_nonneg hδ hA.le)
    obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
    have hpq : p + q = 1 := endpoint_weights_sum (ne_of_gt (by linarith : 0 < a+b))
    have hwlo : 0 ≤ χ.1.1 (φ lo) := χ.1.2.1 (φ lo) (hpos lo)
    have hwhi : 0 ≤ χ.1.1 (φ hi) := χ.1.2.1 (φ hi) (hpos hi)
    have hnewlo : 0 ≤ (functionalMap lam χ).1.1 (φ lo) :=
      (functionalMap lam χ).1.2.1 (φ lo) (hpos lo)
    have hnewhi : 0 ≤ (functionalMap lam χ).1.1 (φ hi) :=
      (functionalMap lam χ).1.2.1 (φ hi) (hpos hi)
    have hleft : (functionalMap lam χ).1.1 (φ lo) ≤
        s^2 * χ.1.1 (φ lo) / functionalGrowthSq lam χ := by
      rw [(functional_map_regular lam χ hR).1]
      apply functional_reweight_band_bound χ.1 lam (φ lo) u s (hpos lo) _ hR
      intro x hx
      exact lower_band_multiplier_bound hA hAa hmean.1 (hlo x hx).1 (hlo x hx).2
    have hright : (functionalMap lam χ).1.1 (φ hi) ≤
        t^2 * χ.1.1 (φ hi) / functionalGrowthSq lam χ := by
      rw [(functional_map_regular lam χ hR).1]
      apply functional_reweight_band_bound χ.1 lam (φ hi) u t (hpos hi) _ hR
      intro x hx
      exact upper_band_multiplier_bound hA (hAa.trans hmean.1) hmean.2
        (hhi x hx).1 (hhi x hx).2
    have hupperlo : 0 ≤ s^2 * χ.1.1 (φ lo) / functionalGrowthSq lam χ :=
      div_nonneg (mul_nonneg (sq_nonneg _) hwlo) hR.le
    have hproduct : 0 ≤ s^p * t^q :=
      mul_nonneg (Real.rpow_nonneg hs _) (Real.rpow_nonneg ht _)
    calc
      functionalGrowthSq lam χ * bandLyapunov φ a b lo hi (functionalMap lam χ) ≤
          functionalGrowthSq lam χ *
            ((s^2 * χ.1.1 (φ lo) / functionalGrowthSq lam χ)^p *
             (t^2 * χ.1.1 (φ hi) / functionalGrowthSq lam χ)^q) := by
        apply mul_le_mul_of_nonneg_left _ hR.le
        exact mul_le_mul (Real.rpow_le_rpow hnewlo hleft hp.le)
          (Real.rpow_le_rpow hnewhi hright hq.le)
          (Real.rpow_nonneg hnewhi _) (Real.rpow_nonneg hupperlo _)
      _ = (s^p * t^q)^2 * bandLyapunov φ a b lo hi χ :=
        power_weight_update_identity s t _ _ _ p q hs ht hwlo hwhi hR hpq
      _ ≤ ρ^2 * bandLyapunov φ a b lo hi χ := by
        apply mul_le_mul_of_nonneg_right _ hV
        exact pow_le_pow_left hproduct hscalar 2
  · have hRzero : functionalGrowthSq lam χ = 0 :=
      le_antisymm (le_of_not_gt hR) (functional_growth_sq_nonneg lam χ)
    rw [hRzero, zero_mul]
    exact mul_nonneg (sq_nonneg _) hV

end BB
