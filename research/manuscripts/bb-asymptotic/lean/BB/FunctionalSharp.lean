import BB.FunctionalBands
import BB.BandPartition

/-!
# A dimension-independent sharp scalar envelope

One finite continuous partition of unity is chosen on the common scalar
interval. Induction removes zero-mass band indices, rather than spectral
atoms. The resulting compact-state envelope therefore applies uniformly to
all positive normalized functionals, including nonatomic distributions.
-/

noncomputable section

open Set
open scoped BigOperators Topology

namespace BB

variable {K ι : Type*} [TopologicalSpace K] [CompactSpace K] [Fintype ι] [DecidableEq ι]

theorem functional_band_face_uniform_rate
    (lam : C(K, ℝ)) (φ : ι → C(K, ℝ)) (center : ι → ℝ)
    (A B γ δ ρ : ℝ) (hA : 0 < A) (hAB : A < B) (hδ : 0 < δ)
    (hρ : 0 < ρ) (hργ : ρ < γ)
    (hlam : ∀ x, A ≤ lam x ∧ lam x ≤ B)
    (hcenter : ∀ i, A ≤ center i ∧ center i ≤ B)
    (hpos : ∀ i x, 0 ≤ φ i x) (hsum : ∑ i, φ i = 1)
    (hsupport : ∀ i x, φ i x ≠ 0 → |lam x-center i| < δ/2)
    (hscalar : ∀ a b u : ℝ, A ≤ a → a ≤ u → u ≤ b → b ≤ B →
      bandEndpointProduct A a b u δ ≤ ρ)
    (I : Finset ι) :
    ∃ C : ℝ, 0 < C ∧ ∃ η : ℝ, 0 < η ∧ η < γ ∧
      ∀ n (χ : BandFace φ I), bandFacePrefix lam φ I n χ ≤ C * η^n := by
  classical
  have hγ : 0 < γ := hρ.trans hργ
  refine Finset.strongInductionOn I ?_
  intro I ih
  by_cases hface : Nonempty (BandFace φ I)
  · letI : Nonempty (BandFace φ I) := hface
    let χ₀ : BandFace φ I := Classical.choice hface
    have hI : I.Nonempty :=
      support_nonempty (band_weights_simplex φ hpos hsum χ₀.1.1) χ₀.2.1
    obtain ⟨lo, hloI, hmin⟩ := I.exists_min_image center hI
    obtain ⟨hi, hhiI, hmax⟩ := I.exists_max_image center hI
    let a : ℝ := max A (center lo-δ/2)
    let b : ℝ := min B (center hi+δ/2)
    have hAa : A ≤ a := le_max_left _ _
    have hbB : b ≤ B := min_le_left _ _
    have ha : 0 < a := hA.trans_le hAa
    have hab : a < b := by
      apply max_lt_iff.mpr
      constructor
      · exact lt_min hAB (by linarith [(hcenter hi).1])
      · exact lt_min (by linarith [(hcenter lo).2]) (by linarith [hmin hi hhiI])
    have hactive : ∀ i ∈ I, ∀ x, φ i x ≠ 0 → a ≤ lam x ∧ lam x ≤ b := by
      intro i hi x hx
      obtain ⟨hleft, hright⟩ := abs_lt.mp (hsupport i x hx)
      refine ⟨max_le (hlam x).1 ?_, le_min (hlam x).2 ?_⟩
      · linarith [hmin i hi]
      · linarith [hmax i hi]
    have hloBand : ∀ x, φ lo x ≠ 0 → a ≤ lam x ∧ lam x ≤ a+δ := by
      intro x hx
      refine ⟨(hactive lo hloI x hx).1, ?_⟩
      have hbnd := (abs_lt.mp (hsupport lo x hx)).2
      have hmaxa : center lo-δ/2 ≤ a := le_max_right _ _
      linarith
    have hhiBand : ∀ x, φ hi x ≠ 0 → b-δ ≤ lam x ∧ lam x ≤ b := by
      intro x hx
      refine ⟨?_, (hactive hi hhiI x hx).2⟩
      have hbnd := (abs_lt.mp (hsupport hi x hx)).1
      have hminb : b ≤ center hi+δ/2 := min_le_right _ _
      linarith
    let V : BandFace φ I → ℝ := fun χ => bandLyapunov φ a b lo hi χ.1
    have hV : Continuous V :=
      (band_lyapunov_continuous φ ha hab lo hi).comp continuous_subtype_val
    have hVpos : ∀ χ, 0 ≤ V χ := fun χ => band_lyapunov_nonneg φ hpos a b lo hi χ.1
    have hstep : ∀ χ : BandFace φ I,
        functionalGrowth lam χ.1 ^ 2 * V (bandFaceMap lam φ hpos I χ) ≤ ρ^2 * V χ := by
      intro χ
      have hau : a ≤ functionalMean lam χ.1 :=
        functional_mean_lower_on_bands χ.1.2 lam φ hpos hsum I χ.2.2 a
          (fun i hi x hx => (hactive i hi x hx).1)
      have hub : functionalMean lam χ.1 ≤ b :=
        functional_mean_upper_on_bands χ.1.2 lam φ hpos hsum I χ.2.2 b
          (fun i hi x hx => (hactive i hi x hx).2)
      exact functional_band_lyapunov_step lam φ hpos lo hi A a b δ ρ hA hAa hab hδ.le
        χ.1 ⟨hau, hub⟩ hloBand hhiBand (hscalar a b _ hAa hau hub hbB)
    have hlyap : ∀ n (χ : BandFace φ I),
        bandFacePrefix lam φ I n χ ^ 2 * V ((bandFaceMap lam φ hpos I)^[n] χ) ≤
          (ρ^2)^n * V χ := by
      intro n χ
      rw [band_face_prefix_eq_product lam φ hpos]
      exact prefix_product_lyapunov (fun χ : BandFace φ I => functionalGrowth lam χ.1)
        (bandFaceMap lam φ hpos I) V (ρ^2) (sq_nonneg _) hstep n χ
    have hboundary : ∀ χ : BandFace φ I, V χ = 0 →
        ∃ n : ℕ, 0 < n ∧ bandFacePrefix lam φ I n χ < γ^n := by
      intro χ hVzero
      by_cases hR : 0 < functionalGrowthSq lam χ.1
      · let J := positiveSupport (bandWeights φ χ.1.1)
        have hzero : χ.1.1.1 (φ lo) = 0 ∨ χ.1.1.1 (φ hi) = 0 :=
          (band_lyapunov_eq_zero_iff φ hpos ha hab lo hi χ.1).mp hVzero
        have hJI : J ⊂ I := by
          rcases hzero with hlozero | hhizero
          · exact positiveSupport_proper_of_zero χ.2.1 hloI hlozero
          · exact positiveSupport_proper_of_zero χ.2.1 hhiI hhizero
        obtain ⟨C, _hC, η, hη, hηγ, henv⟩ := ih J hJI
        let ξ : BandFace φ J :=
          ⟨functionalMap lam χ.1,
            functional_regular_image_in_band_support lam φ hpos hsum χ.1 hR⟩
        have htail : ∀ n, prefixProduct (functionalGrowth lam) (functionalMap lam) n
            (functionalMap lam χ.1) ≤ C * η^n := fun n => henv n ξ
        exact strict_prefix_of_tail_envelope (functionalGrowth lam) (functionalMap lam) χ.1
          (functional_growth_nonneg lam χ.1) C η γ hη.le hγ hηγ htail
      · have hRzero : functionalGrowthSq lam χ.1 = 0 :=
          le_antisymm (le_of_not_gt hR) (functional_growth_sq_nonneg lam χ.1)
        have hr : functionalGrowth lam χ.1 = 0 := by simp [functionalGrowth, hRzero]
        refine ⟨1, by omega, ?_⟩
        change prefixProduct (functionalGrowth lam) (functionalMap lam) 1 χ.1 < γ^1
        simpa only [prefix_product_succ, prefix_product_zero, hr, zero_mul, pow_one] using hγ
    exact compact_boundary_lyapunov_improved_rate (bandFaceMap lam φ hpos I)
      (bandFacePrefix lam φ I) (fun χ => rfl)
      (fun n => (functional_prefix_continuous lam A B hA hAB.le hlam n).comp continuous_subtype_val)
      (fun n χ => prefix_product_nonneg (functionalGrowth lam) (functionalMap lam)
        (functional_growth_nonneg lam) n χ.1)
      (band_face_prefix_cocycle lam φ hpos I) V hV hVpos (ρ^2) γ
      (sq_nonneg _) hγ (by nlinarith) hlyap hboundary
  · refine ⟨1, zero_lt_one, γ/2, by linarith, by linarith, ?_⟩
    intro n χ
    exact (hface ⟨χ⟩).elim

theorem functional_envelope_of_band_partition
    (lam : C(K, ℝ)) (φ : ι → C(K, ℝ)) (center : ι → ℝ)
    (A B γ δ ρ : ℝ) (hA : 0 < A) (hAB : A < B) (hδ : 0 < δ)
    (hρ : 0 < ρ) (hργ : ρ < γ)
    (hlam : ∀ x, A ≤ lam x ∧ lam x ≤ B)
    (hcenter : ∀ i, A ≤ center i ∧ center i ≤ B)
    (hpos : ∀ i x, 0 ≤ φ i x) (hsum : ∑ i, φ i = 1)
    (hsupport : ∀ i x, φ i x ≠ 0 → |lam x-center i| < δ/2)
    (hscalar : ∀ a b u : ℝ, A ≤ a → a ≤ u → u ≤ b → b ≤ B →
      bandEndpointProduct A a b u δ ≤ ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (χ : FunctionalState K),
      prefixProduct (functionalGrowth lam) (functionalMap lam) n χ ≤ C * γ^n := by
  classical
  obtain ⟨C, hC, η, hη, hηγ, henv⟩ := functional_band_face_uniform_rate lam φ center
    A B γ δ ρ hA hAB hδ hρ hργ hlam hcenter hpos hsum hsupport hscalar Finset.univ
  refine ⟨C, hC, ?_⟩
  intro n χ
  have hχ : InBandFace φ Finset.univ χ := by
    constructor <;> intro i hi <;> exact (hi (Finset.mem_univ i)).elim
  exact (henv n ⟨χ, hχ⟩).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left hη.le hηγ.le n) hC.le)

def intervalCoordinate (A B : ℝ) : C(Icc A B, ℝ) :=
  ⟨Subtype.val, continuous_subtype_val⟩

theorem functional_growth_zero_of_constant (lam : C(K, ℝ)) (a : ℝ)
    (ha : a ≠ 0) (hlam : ∀ x, lam x = a) (χ : FunctionalState K) :
    functionalGrowth lam χ = 0 := by
  have hlamEq : lam = ContinuousMap.const K a := by ext x; exact hlam x
  have hmean : functionalMean lam χ = a := by
    change χ.2.1 lam = a
    rw [hlamEq, positive_unit_const χ.2.2]
  have hq : quadraticMultiplier lam a = 0 := by
    ext x
    rw [quadraticMultiplier_apply, hlam x, div_self ha, sub_self, zero_pow (by decide : 2 ≠ 0)]
    rfl
  simp only [functionalGrowth, functionalGrowthSq, hmean, hq, map_zero, Real.sqrt_zero]

/-- The same prefactor works for every pair of positive normalized
functionals on the fixed interval. It depends only on the scalar interval
and the requested rate. -/
theorem interval_functional_envelope (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hγ : rate A B < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (χ : FunctionalState (Icc A B)),
      prefixProduct (functionalGrowth (intervalCoordinate A B))
        (functionalMap (intervalCoordinate A B)) n χ ≤ C * γ^n := by
  classical
  rcases lt_or_eq_of_le hAB with hAB | hAB
  · obtain ⟨δ, ρ, hδ, hρ, hργ, hscalar⟩ := uniform_endpoint_band_bound A B γ hA hAB.le hγ
    obtain ⟨s, φ, hpos, hsum, hsupport⟩ := interval_band_partition A B (δ/2) (half_pos hδ)
    exact functional_envelope_of_band_partition (intervalCoordinate A B) φ
      (fun i => (i : Icc A B).1) A B γ δ ρ hA hAB hδ hρ hργ
      (fun x => x.2) (fun i => (i : Icc A B).2) hpos hsum hsupport hscalar
  · subst B
    have hγpos : 0 < γ := by simpa only [rate, sub_self, zero_div] using hγ
    refine ⟨1, zero_lt_one, ?_⟩
    intro n χ
    cases n with
    | zero => simp only [prefix_product_zero, pow_zero, mul_one, le_refl]
    | succ n =>
      have hr : functionalGrowth (intervalCoordinate A A) χ = 0 :=
        functional_growth_zero_of_constant _ A (ne_of_gt hA)
          (fun x => le_antisymm x.2.2 x.2.1) χ
      rw [prefix_product_terminal _ _ χ hr]
      positivity

/-- The same argument applies to a continuous spectral coordinate on any
compact space, by pulling the interval partition back along that coordinate. -/
theorem compact_coordinate_functional_envelope (lam : C(K,ℝ)) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ x, A ≤ lam x ∧ lam x ≤ B)
    (hγ : rate A B < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (χ : FunctionalState K),
      prefixProduct (functionalGrowth lam) (functionalMap lam) n χ ≤ C*γ^n := by
  classical
  rcases hAB.lt_or_eq with hABlt | hABeq
  · obtain ⟨δ,ρ,hδ,hρ,hργ,hscalar⟩ := uniform_endpoint_band_bound A B γ hA hAB hγ
    obtain ⟨s,φ,hpos,hsum,hsupport⟩ := interval_band_partition A B (δ/2) (half_pos hδ)
    let coord : C(K,Icc A B) := ⟨fun x => ⟨lam x,hlam x⟩,lam.continuous.subtype_mk hlam⟩
    let φ' : s → C(K,ℝ) := fun i => (φ i).comp coord
    have hsum' : ∑ i, φ' i = 1 := by
      ext x
      have h := congrArg (fun f : C(Icc A B,ℝ) => f (coord x)) hsum
      simpa only [ContinuousMap.sum_apply, ContinuousMap.one_apply] using h
    exact functional_envelope_of_band_partition lam φ' (fun i => (i : Icc A B).1)
      A B γ δ ρ hA hABlt hδ hρ hργ hlam (fun i => (i : Icc A B).2)
      (fun i x => hpos i (coord x)) hsum'
      (fun i x hx => hsupport i (coord x) hx) hscalar
  · subst B
    have hγpos : 0 < γ := by simpa only [rate, sub_self, zero_div] using hγ
    refine ⟨1,zero_lt_one,?_⟩
    intro n χ
    cases n with
    | zero => simp only [prefix_product_zero,pow_zero,mul_one,le_refl]
    | succ n =>
      have hr := functional_growth_zero_of_constant lam A hA.ne'
        (fun x => le_antisymm (hlam x).2 (hlam x).1) χ
      rw [prefix_product_terminal _ _ χ hr]
      positivity

end BB
