import BB.Spectral
import BB.Cocycle
import Mathlib.Topology.Instances.Real

/-! # Compact finite spectral state space and actual terminal update -/

namespace BB
noncomputable section
open Filter Set
open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι]

abbrev Simplex (ι : Type*) [Fintype ι] := { w : ι → ℝ // IsSimplex w }
abbrev SpectralState (ι : Type*) [Fintype ι] := Simplex ι × Simplex ι

private theorem coordinate_le_one {w : ι → ℝ} (hw : IsSimplex w) (i : ι) : w i ≤ 1 := by
  rw [← hw.2]
  exact Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)

theorem simplex_isClosed : IsClosed {w : ι → ℝ | IsSimplex w} := by
  have hnonneg : IsClosed {w : ι → ℝ | ∀ i, 0 ≤ w i} := by
    have heq : {w : ι → ℝ | ∀ i, 0 ≤ w i} = ⋂ i : ι, {w : ι → ℝ | 0 ≤ w i} := by
      ext w
      simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have hsum : Continuous (fun w : ι → ℝ => ∑ i, w i) :=
    continuous_finset_sum _ (fun i _ => continuous_apply i)
  exact hnonneg.inter (isClosed_eq hsum continuous_const)

theorem simplex_isCompact : IsCompact {w : ι → ℝ | IsSimplex w} := by
  apply (isCompact_Icc : IsCompact (Icc (fun _ : ι => (0 : ℝ)) (fun _ : ι => (1 : ℝ)))).of_isClosed_subset
    simplex_isClosed
  intro w hw
  exact ⟨hw.1,coordinate_le_one hw⟩

instance : CompactSpace (Simplex ι) := isCompact_iff_compactSpace.mp simplex_isCompact

instance [Nonempty ι] : Nonempty (Simplex ι) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  let w : ι → ℝ := fun i => if i = i₀ then 1 else 0
  refine ⟨⟨w,?_,?_⟩⟩
  · intro i
    dsimp only [w]
    split_ifs <;> norm_num
  · simp [w]

def stateGrowthSq (lam : ι → ℝ) (χ : SpectralState ι) : ℝ :=
  growthSq lam χ.1.1 χ.2.1

def stateGrowth (lam : ι → ℝ) (χ : SpectralState ι) : ℝ :=
  Real.sqrt (stateGrowthSq lam χ)

/-- The choice `χ` at a terminal state is immaterial for every positive-length product. -/
def spectralMap (lam : ι → ℝ) (χ : SpectralState ι) : SpectralState ι :=
  if h : 0 < stateGrowthSq lam χ then
    (⟨weightUpdate lam χ.1.1 χ.2.1, weight_update_simplex χ.1.2 h⟩, χ.1)
  else χ

theorem state_growth_nonneg (lam : ι → ℝ) (χ : SpectralState ι) : 0 ≤ stateGrowth lam χ :=
  Real.sqrt_nonneg _

theorem state_mean_continuous (lam : ι → ℝ) :
    Continuous (fun χ : SpectralState ι => mean lam χ.2.1) := by
  unfold mean
  apply continuous_finset_sum
  intro i _
  exact continuous_const.mul ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))

theorem state_mean_pos (lam : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) (χ : SpectralState ι) : 0 < mean lam χ.2.1 :=
  ha.trans_le (mean_lower χ.2.2 hlam)

theorem state_growth_sq_continuous (lam : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) : Continuous (stateGrowthSq lam) := by
  have hm := state_mean_continuous lam
  have hm0 : ∀ χ : SpectralState ι, mean lam χ.2.1 ≠ 0 :=
    fun χ => ne_of_gt (state_mean_pos lam a ha hlam χ)
  unfold stateGrowthSq growthSq multiplier
  apply continuous_finset_sum
  intro i _
  apply Continuous.mul
  · exact (continuous_const.sub (continuous_const.div hm hm0)).pow 2
  · exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)

theorem state_growth_continuous (lam : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) : Continuous (stateGrowth lam) :=
  (state_growth_sq_continuous lam a ha hlam).sqrt

theorem state_growth_bound (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (χ : SpectralState ι) : stateGrowth lam χ ≤ 1 + b/a := by
  let u := mean lam χ.2.1
  have hua : a ≤ u := mean_lower χ.2.2 (fun i => (hlam i).1)
  have hu : 0 < u := ha.trans_le hua
  have hb : 0 < b := ha.trans_le hab
  have hC : 0 ≤ 1+b/a := by positivity
  have hphi : ∀ i, multiplier lam u i ≤ (1+b/a)^2 := by
    intro i
    have hnum : 0 ≤ lam i := (le_of_lt ha).trans (hlam i).1
    have hratio0 : 0 ≤ lam i/u := div_nonneg hnum (le_of_lt hu)
    have hratio : lam i/u ≤ b/a := by
      apply (div_le_div_iff hu ha).mpr
      exact (mul_le_mul_of_nonneg_right (hlam i).2 (le_of_lt ha)).trans
        (mul_le_mul_of_nonneg_left hua (le_of_lt hb))
    have hq : |1-lam i/u| ≤ 1+b/a := by
      apply abs_le.mpr
      constructor <;> linarith
    unfold multiplier
    exact (sq_abs (1-lam i/u)).symm.le.trans
      (pow_le_pow_left (abs_nonneg _) hq 2)
  have hsum : stateGrowthSq lam χ ≤ (1+b/a)^2 := by
    unfold stateGrowthSq growthSq
    calc
      (∑ i, multiplier lam (mean lam χ.2.1) i * χ.1.1 i) ≤
          ∑ i, (1+b/a)^2 * χ.1.1 i :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hphi i) (χ.1.2.1 i)
      _ = (1+b/a)^2 := by rw [← Finset.mul_sum, χ.1.2.2, mul_one]
  calc
    stateGrowth lam χ ≤ Real.sqrt ((1+b/a)^2) := Real.sqrt_le_sqrt hsum
    _ = 1+b/a := Real.sqrt_sq hC

theorem spectral_map_regular (lam : ι → ℝ) (χ : SpectralState ι)
    (hχ : 0 < stateGrowthSq lam χ) :
    (spectralMap lam χ).1.1 = weightUpdate lam χ.1.1 χ.2.1 ∧
      (spectralMap lam χ).2 = χ.1 := by
  simp only [spectralMap,dif_pos hχ]
  exact ⟨trivial,trivial⟩

theorem spectral_map_continuousAt_regular (lam : ι → ℝ) (a : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i) (χ : SpectralState ι)
    (hχ : stateGrowth lam χ ≠ 0) : ContinuousAt (spectralMap lam) χ := by
  have hR : 0 < stateGrowthSq lam χ :=
    lt_of_le_of_ne (growth_sq_nonneg χ.1.2) (fun hz => hχ (by simp [stateGrowth,hz.symm]))
  have hRcont := state_growth_sq_continuous lam a ha hlam
  have hreg : ∀ᶠ y in 𝓝 χ, 0 < stateGrowthSq lam y :=
    (isOpen_lt continuous_const hRcont).mem_nhds hR
  have hden : mean lam χ.2.1 ≠ 0 := ne_of_gt (state_mean_pos lam a ha hlam χ)
  have hwcont : ContinuousAt (fun y : SpectralState ι => weightUpdate lam y.1.1 y.2.1) χ := by
    apply continuousAt_pi.mpr
    intro i
    unfold weightUpdate multiplier
    apply ContinuousAt.div
    · apply ContinuousAt.mul
      · exact (continuousAt_const.sub (continuousAt_const.div
          (state_mean_continuous lam).continuousAt hden)).pow 2
      · exact ((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).continuousAt
    · exact hRcont.continuousAt
    · exact ne_of_gt hR
  have hfirst : ContinuousAt (fun y => (spectralMap lam y).1) χ := by
    change Tendsto _ (𝓝 χ) (𝓝 _)
    rw [tendsto_subtype_rng]
    have he : (fun y : SpectralState ι => (spectralMap lam y).1.1) =ᶠ[𝓝 χ]
        (fun y => weightUpdate lam y.1.1 y.2.1) := by
      filter_upwards [hreg] with y hy
      exact (spectral_map_regular lam y hy).1
    rw [(spectral_map_regular lam χ hR).1]
    exact (tendsto_congr' he).mpr hwcont
  have hsecond : ContinuousAt (fun y => (spectralMap lam y).2) χ := by
    have he : (fun y : SpectralState ι => (spectralMap lam y).2) =ᶠ[𝓝 χ] (fun y => y.1) := by
      filter_upwards [hreg] with y hy
      exact (spectral_map_regular lam y hy).2
    change Tendsto _ (𝓝 χ) (𝓝 ((spectralMap lam χ).2))
    rw [(spectral_map_regular lam χ hR).2]
    exact (tendsto_congr' he).mpr continuous_fst.continuousAt
  exact hfirst.prod hsecond

theorem spectral_prefix_continuous (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (n : ℕ) :
    Continuous (prefixProduct (stateGrowth lam) (spectralMap lam) n) := by
  have hb : 0 < b := ha.trans_le hab
  exact prefix_product_continuous (stateGrowth lam) (spectralMap lam) (1+b/a)
    (by positivity) (state_growth_nonneg lam) (state_growth_bound lam a b ha hab hlam)
    (state_growth_continuous lam a ha (fun i => (hlam i).1))
    (spectral_map_continuousAt_regular lam a ha (fun i => (hlam i).1)) n

end
end BB
