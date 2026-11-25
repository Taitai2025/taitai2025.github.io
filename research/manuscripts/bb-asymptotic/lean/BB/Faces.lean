import BB.SpectralTopology

/-! # Closed invariant faces of the finite spectral state -/

namespace BB
noncomputable section
open scoped BigOperators Topology
open Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def SupportedOn (I : Finset ι) (w : ι → ℝ) : Prop := ∀ i, i ∉ I → w i = 0
def InFace (I : Finset ι) (χ : SpectralState ι) : Prop :=
  SupportedOn I χ.1.1 ∧ SupportedOn I χ.2.1
abbrev SpectralFace (I : Finset ι) := {χ : SpectralState ι // InFace I χ}

def positiveSupport (w : ι → ℝ) : Finset ι := Finset.univ.filter (fun i => 0 < w i)

theorem supported_positiveSupport {w : ι → ℝ} (hw : IsSimplex w) :
    SupportedOn (positiveSupport w) w := by
  intro i hi
  have hnp : ¬0 < w i := by simpa [positiveSupport] using hi
  exact le_antisymm (le_of_not_gt hnp) (hw.1 i)

theorem positiveSupport_nonempty {w : ι → ℝ} (hw : IsSimplex w) :
    (positiveSupport w).Nonempty := by
  by_contra he
  have hempty : positiveSupport w = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
  have hzero : ∀ i, w i = 0 := by
    intro i
    exact supported_positiveSupport hw i (by simp [hempty])
  have hs := hw.2
  simp only [hzero,Finset.sum_const_zero] at hs
  norm_num at hs

theorem positiveSupport_subset {I : Finset ι} {w : ι → ℝ}
    (hsupp : SupportedOn I w) : positiveSupport w ⊆ I := by
  intro i hi
  have hip : 0 < w i := by simpa [positiveSupport] using hi
  by_contra hni
  rw [hsupp i hni] at hip
  exact lt_irrefl _ hip

theorem support_nonempty {I : Finset ι} {w : ι → ℝ}
    (hw : IsSimplex w) (hsupp : SupportedOn I w) : I.Nonempty :=
  (positiveSupport_nonempty hw).mono (positiveSupport_subset hsupp)

theorem supported_mean_lower {I : Finset ι} {lam w : ι → ℝ} {a : ℝ}
    (hw : IsSimplex w) (hsupp : SupportedOn I w)
    (hlam : ∀ i ∈ I, a ≤ lam i) : a ≤ mean lam w := by
  calc
    a = ∑ i, a*w i := by rw [← Finset.mul_sum,hw.2,mul_one]
    _ ≤ ∑ i, lam i*w i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ I
      · exact mul_le_mul_of_nonneg_right (hlam i hi) (hw.1 i)
      · simp only [hsupp i hi,mul_zero,le_refl]

theorem supported_mean_upper {I : Finset ι} {lam w : ι → ℝ} {b : ℝ}
    (hw : IsSimplex w) (hsupp : SupportedOn I w)
    (hlam : ∀ i ∈ I, lam i ≤ b) : mean lam w ≤ b := by
  calc
    (∑ i, lam i*w i) ≤ ∑ i, b*w i := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ I
      · exact mul_le_mul_of_nonneg_right (hlam i hi) (hw.1 i)
      · simp only [hsupp i hi,mul_zero,le_refl]
    _ = b := by rw [← Finset.mul_sum,hw.2,mul_one]

theorem supportedOn_isClosed (I : Finset ι) : IsClosed {w : ι → ℝ | SupportedOn I w} := by
  have heq : {w : ι → ℝ | SupportedOn I w} = ⋂ i : {i // i ∉ I}, {w : ι → ℝ | w i = 0} := by
    ext w
    simp [SupportedOn]
  rw [heq]
  exact isClosed_iInter fun i => isClosed_eq (continuous_apply i.1) continuous_const

theorem face_isClosed (I : Finset ι) : IsClosed {χ : SpectralState ι | InFace I χ} :=
  ((supportedOn_isClosed I).preimage (continuous_subtype_val.comp continuous_fst)).inter
    ((supportedOn_isClosed I).preimage (continuous_subtype_val.comp continuous_snd))

instance (I : Finset ι) : CompactSpace (SpectralFace I) :=
  isCompact_iff_compactSpace.mp (face_isClosed I).isCompact

theorem spectral_map_preserves_face (lam : ι → ℝ) (I : Finset ι)
    (χ : SpectralState ι) (hχ : InFace I χ) : InFace I (spectralMap lam χ) := by
  unfold spectralMap
  split_ifs with hR
  · constructor
    · intro i hi
      exact weight_update_zero (hχ.1 i hi)
    · exact hχ.1
  · exact hχ

def faceMap (lam : ι → ℝ) (I : Finset ι) (χ : SpectralFace I) : SpectralFace I :=
  ⟨spectralMap lam χ.1,spectral_map_preserves_face lam I χ.1 χ.2⟩

def facePrefix (lam : ι → ℝ) (I : Finset ι) (n : ℕ) (χ : SpectralFace I) : ℝ :=
  prefixProduct (stateGrowth lam) (spectralMap lam) n χ.1

theorem face_iterate_val (lam : ι → ℝ) (I : Finset ι) (n : ℕ) (χ : SpectralFace I) :
    ((faceMap lam I)^[n] χ).1 = (spectralMap lam)^[n] χ.1 := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply,Function.iterate_succ_apply,ih]
    rfl

theorem face_prefix_cocycle (lam : ι → ℝ) (I : Finset ι) (n m : ℕ) (χ : SpectralFace I) :
    facePrefix lam I (n+m) χ = facePrefix lam I n χ *
      facePrefix lam I m ((faceMap lam I)^[n] χ) := by
  unfold facePrefix
  rw [prefix_product_cocycle,face_iterate_val]

theorem face_prefix_eq_product (lam : ι → ℝ) (I : Finset ι) (n : ℕ) (χ : SpectralFace I) :
    facePrefix lam I n χ = prefixProduct (fun y : SpectralFace I => stateGrowth lam y.1)
      (faceMap lam I) n χ := by
  induction n generalizing χ with
  | zero => rfl
  | succ n ih =>
    change stateGrowth lam χ.1 * facePrefix lam I n (faceMap lam I χ) = _
    rw [ih]
    rfl

theorem face_prefix_continuous (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (I : Finset ι) (n : ℕ) :
    Continuous (facePrefix lam I n) :=
  (spectral_prefix_continuous lam a b ha hab hlam n).comp continuous_subtype_val

theorem regular_image_in_current_support (lam : ι → ℝ) (χ : SpectralState ι)
    (hR : 0 < stateGrowthSq lam χ) :
    InFace (positiveSupport χ.1.1) (spectralMap lam χ) := by
  obtain ⟨hfirst,hsecond⟩ := spectral_map_regular lam χ hR
  constructor
  · intro i hi
    rw [hfirst]
    exact weight_update_zero (supported_positiveSupport χ.1.2 i hi)
  · rw [hsecond]
    exact supported_positiveSupport χ.1.2

theorem positiveSupport_proper_of_zero {I : Finset ι} {w : ι → ℝ} {j : ι}
    (hsupp : SupportedOn I w) (hj : j ∈ I) (hwj : w j = 0) :
    positiveSupport w ⊂ I := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨positiveSupport_subset hsupp,?_⟩
  intro he
  have hin : j ∈ positiveSupport w := he.symm ▸ hj
  have hp : 0 < w j := by simpa [positiveSupport] using hin
  rw [hwj] at hp
  exact lt_irrefl _ hp

theorem singleton_mean {lam w : ι → ℝ} {j : ι}
    (hw : IsSimplex w) (hsupp : SupportedOn {j} w) : mean lam w = lam j := by
  have hsum : (∑ i, w i) = w j := by
    apply Finset.sum_eq_single j
    · intro i _ hne
      exact hsupp i (by simpa only [Finset.mem_singleton] using hne)
    · simp
  have hwj : w j = 1 := hsum.symm.trans hw.2
  unfold mean
  rw [Finset.sum_eq_single j]
  · rw [hwj,mul_one]
  · intro i _ hne
    rw [hsupp i (by simpa only [Finset.mem_singleton] using hne),mul_zero]
  · simp

theorem singleton_face_terminal (lam : ι → ℝ) (j : ι) (hj : lam j ≠ 0)
    (χ : SpectralFace {j}) : stateGrowthSq lam χ.1 = 0 := by
  have hm := singleton_mean (lam := lam) χ.1.2.2 χ.2.2
  unfold stateGrowthSq growthSq multiplier
  rw [hm]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i = j
  · subst i
    simp [div_self hj]
  · rw [χ.2.1 i (by simpa only [Finset.mem_singleton] using hi),mul_zero]

theorem constant_face_terminal (lam : ι → ℝ) (I : Finset ι) (a : ℝ) (ha : a ≠ 0)
    (hlam : ∀ i ∈ I, lam i = a) (χ : SpectralFace I) : stateGrowthSq lam χ.1 = 0 := by
  have hm : mean lam χ.1.2.1 = a := le_antisymm
    (supported_mean_upper χ.1.2.2 χ.2.2 (fun i hi => (hlam i hi).le))
    (supported_mean_lower χ.1.2.2 χ.2.2 (fun i hi => (hlam i hi).ge))
  unfold stateGrowthSq growthSq multiplier
  rw [hm]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i ∈ I
  · rw [hlam i hi,div_self ha,sub_self,zero_pow (by decide : 2 ≠ 0),zero_mul]
  · rw [χ.2.1 i hi,mul_zero]

end
end BB
