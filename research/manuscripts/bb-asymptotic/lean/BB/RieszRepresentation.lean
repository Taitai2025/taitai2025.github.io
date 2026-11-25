import BB.HilbertProbability
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani
import Mathlib.MeasureTheory.Measure.Content
import Mathlib.Topology.UrysohnsBounded

/-!
# Riesz representation for positive normalized functionals on compact spaces

This file completes the compact-space content construction available in mathlib
4.8.0: disjoint additivity, regularity, and integral representation. In particular
no measure-representation hypothesis is used in the final theorem.
-/

noncomputable section
namespace BB
open MeasureTheory Set TopologicalSpace BoundedContinuousFunction
open scoped Topology NNReal ENNReal

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

/-- A nonnegative bounded continuous function, viewed as a real continuous map. -/
def nnContinuousReal (f : K →ᵇ ℝ≥0) : C(K, ℝ) :=
  ⟨fun x => (f x : ℝ), NNReal.continuous_coe.comp f.continuous⟩

@[simp] theorem nnContinuousReal_apply (f : K →ᵇ ℝ≥0) (x : K) :
    nnContinuousReal f x = (f x : ℝ) := rfl

/-- A continuous real map with nonnegative values, bundled with nonnegative codomain. -/
def nonnegativeContinuous (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x) : K →ᵇ ℝ≥0 :=
  BoundedContinuousFunction.mkOfCompact
    ⟨fun x => ⟨f x, hf x⟩, f.continuous.subtype_mk _⟩

@[simp] theorem nnContinuousReal_nonnegative (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x) :
    nnContinuousReal (nonnegativeContinuous f hf) = f := by ext x; rfl

/-- Restriction of a positive real functional to nonnegative continuous functions. -/
def positiveNNFunctional (L : PositiveState K) : (K →ᵇ ℝ≥0) →ₗ[ℝ≥0] ℝ≥0 where
  toFun f := ⟨L.1 (nnContinuousReal f), L.2.1 _ (fun x => (f x).coe_nonneg)⟩
  map_add' f g := by
    apply Subtype.ext
    change L.1 (nnContinuousReal (f + g)) = L.1 (nnContinuousReal f) + L.1 (nnContinuousReal g)
    have h : nnContinuousReal (f + g) = nnContinuousReal f + nnContinuousReal g := by
      ext x
      exact NNReal.coe_add _ _
    rw [h, map_add]
  map_smul' c f := by
    apply Subtype.ext
    change L.1 (nnContinuousReal (c • f)) = (c : ℝ) * L.1 (nnContinuousReal f)
    have h : nnContinuousReal (c • f) = (c : ℝ) • nnContinuousReal f := by
      ext x
      exact NNReal.coe_mul _ _
    rw [h, _root_.map_smul, smul_eq_mul]

@[simp] theorem positiveNNFunctional_coe (L : PositiveState K) (f : K →ᵇ ℝ≥0) :
    (positiveNNFunctional L f : ℝ) = L.1 (nnContinuousReal f) := rfl

@[simp] theorem positiveNNFunctional_one (L : PositiveState K) : positiveNNFunctional L 1 = 1 := by
  apply Subtype.ext
  change L.1 (nnContinuousReal 1) = 1
  have h : nnContinuousReal (1 : K →ᵇ ℝ≥0) = 1 := by ext x; rfl
  rw [h, L.2.2]

/-- Reverse subadditivity on disjoint compact sets follows by a Urysohn split. -/
theorem rieszAux_disjoint [NormalSpace K] (L : PositiveState K)
    (S T : Compacts K) (hd : Disjoint (S : Set K) T)
    (hS : IsClosed (S : Set K)) (hT : IsClosed (T : Set K)) :
    rieszContentAux (positiveNNFunctional L) (S ⊔ T) =
      rieszContentAux (positiveNNFunctional L) S +
      rieszContentAux (positiveNNFunctional L) T := by
  apply le_antisymm (rieszContentAux_sup_le _ _ _)
  apply le_csInf (rieszContentAux_image_nonempty _ _)
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨u, huS, huT, hu⟩ := exists_continuous_zero_one_of_isClosed hS hT hd
  let uS : C(K, ℝ) := 1 - u
  let fS := nonnegativeContinuous (nnContinuousReal f * uS)
    (fun x => mul_nonneg (f x).coe_nonneg (sub_nonneg.mpr (hu x).2))
  let fT := nonnegativeContinuous (nnContinuousReal f * u)
    (fun x => mul_nonneg (f x).coe_nonneg (hu x).1)
  have hSf : ∀ x ∈ S, (1 : ℝ≥0) ≤ fS x := by
    intro x hx
    change (1 : ℝ) ≤ (f x : ℝ) * (1 - u x)
    rw [huS hx]
    simpa using hf x (Or.inl hx)
  have hTf : ∀ x ∈ T, (1 : ℝ≥0) ≤ fT x := by
    intro x hx
    change (1 : ℝ) ≤ (f x : ℝ) * u x
    rw [huT hx]
    simpa using hf x (Or.inr hx)
  have hsum : fS + fT = f := by
    ext x
    change (f x : ℝ) * (1 - u x) + (f x : ℝ) * u x = (f x : ℝ)
    ring
  calc
    _ ≤ positiveNNFunctional L fS + positiveNNFunctional L fT :=
      add_le_add (rieszContentAux_le _ hSf) (rieszContentAux_le _ hTf)
    _ = positiveNNFunctional L f := by rw [← map_add, hsum]

/-- The actual additive compact content attached to a positive state. -/
def positiveContent [NormalSpace K] (L : PositiveState K) : Content K where
  toFun := rieszContentAux (positiveNNFunctional L)
  mono' _ _ h := rieszContentAux_mono _ h
  sup_disjoint' := rieszAux_disjoint L
  sup_le' := rieszContentAux_sup_le _

@[simp] theorem positiveContent_toFun [NormalSpace K] (L : PositiveState K) (S : Compacts K) :
    (positiveContent L).toFun S = rieszContentAux (positiveNNFunctional L) S := rfl

/-- A nonnegative continuous majorant bounds the content from above. -/
theorem positiveContent_le [NormalSpace K] (L : PositiveState K)
    (S : Compacts K) (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hS : ∀ x ∈ S, 1 ≤ f x) :
    ((positiveContent L).toFun S : ℝ) ≤ L.1 f := by
  have h := rieszContentAux_le (positiveNNFunctional L)
    (K := S) (f := nonnegativeContinuous f hf) (by exact hS)
  exact_mod_cast h

/-- A test between zero and one, vanishing outside a compact set, bounds its content below. -/
theorem le_positiveContent [NormalSpace K] (L : PositiveState K)
    (S : Compacts K) (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) (hzero : ∀ x, x ∉ (S : Set K) → f x = 0) :
    L.1 f ≤ ((positiveContent L).toFun S : ℝ) := by
  let v : ℝ≥0 := ⟨L.1 f, L.2.1 f hf⟩
  have h : v ≤ (positiveContent L).toFun S := by
    apply le_csInf (rieszContentAux_image_nonempty _ _)
    rintro _ ⟨g, hg, rfl⟩
    apply (NNReal.coe_le_coe).mp
    change L.1 f ≤ L.1 (nnContinuousReal g)
    apply positive_unit_mono L.2
    intro x
    by_cases hx : x ∈ (S : Set K)
    · exact (hf1 x).trans (by exact_mod_cast hg x hx)
    · rw [hzero x hx]
      exact (g x).coe_nonneg
  exact_mod_cast h


/-- Compact neighborhoods approximate the content from above. -/
theorem positiveContent_enlargement [NormalSpace K] (L : PositiveState K)
    (S : Compacts K) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Compacts K, (S : Set K) ⊆ interior (T : Set K) ∧
      ((positiveContent L).toFun T : ℝ) < (positiveContent L).toFun S + ε := by
  let δ : ℝ≥0 := ⟨ε / 2, (half_pos hε).le⟩
  have hδ : 0 < δ := by exact_mod_cast half_pos hε
  obtain ⟨f, hfS, hf⟩ := exists_lt_rieszContentAux_add_pos (positiveNNFunctional L) S hδ
  let g : C(K, ℝ) := nnContinuousReal f + ContinuousMap.const K (ε / 2)
  have hg : ∀ x, 0 ≤ g x := fun x => add_nonneg (f x).coe_nonneg (half_pos hε).le
  let T : Compacts K := ⟨{x | 1 ≤ g x}, (isClosed_le continuous_const g.continuous).isCompact⟩
  refine ⟨T, ?_, ?_⟩
  · have hsub : {x | 1 < g x} ⊆ (T : Set K) := fun x hx => (show 1 < g x from hx).le
    have hint : {x | 1 < g x} ⊆ interior (T : Set K) :=
      interior_maximal hsub (isOpen_lt continuous_const g.continuous)
    apply Subset.trans _ hint
    intro x hx
    change 1 < (f x : ℝ) + ε / 2
    have hfx : (1 : ℝ) ≤ f x := by exact_mod_cast hfS x hx
    linarith only [hfx, hε]
  · have hmajor := positiveContent_le L T g hg (fun x hx => hx)
    have heval : L.1 g = L.1 (nnContinuousReal f) + ε / 2 := by
      simp only [g, map_add, positive_unit_const L.2]
    have happrox : L.1 (nnContinuousReal f) <
        ((positiveContent L).toFun S : ℝ) + ε / 2 := by exact_mod_cast hf
    rw [heval] at hmajor
    linarith only [hmajor, happrox]

/-- The additive content satisfies the exact regularity needed by Content.measure. -/
theorem positiveContent_regular [NormalSpace K] (L : PositiveState K) :
    (positiveContent L).ContentRegular := by
  intro S
  apply le_antisymm
  · apply le_iInf
    intro T
    apply le_iInf
    intro hST
    exact (positiveContent L).mono S T (hST.trans interior_subset)
  · apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    obtain ⟨T, hST, hT⟩ := positiveContent_enlargement L S (by exact_mod_cast hε : (0 : ℝ) < ε)
    have hT' : (positiveContent L) T ≤ (positiveContent L) S + ε := by
      change ((positiveContent L).toFun T : ℝ≥0∞) ≤ ((positiveContent L).toFun S : ℝ≥0∞) + ε
      exact_mod_cast hT.le
    exact (iInf_le_of_le T (iInf_le _ hST)).trans hT'

section Measure
variable [T2Space K] [NormalSpace K] [MeasurableSpace K] [BorelSpace K]

/-- The measure is obtained from the proved regular additive content. -/
def positiveMeasure (L : PositiveState K) : Measure K := (positiveContent L).measure

theorem positiveMeasure_compact (L : PositiveState K) (S : Compacts K) :
    positiveMeasure L S = (positiveContent L) S :=
  (positiveContent L).measure_eq_content_of_regular (positiveContent_regular L) S

@[simp] theorem positiveContent_univ (L : PositiveState K) :
    (positiveContent L).toFun ⟨univ, isCompact_univ⟩ = 1 := by
  apply le_antisymm
  · simpa using rieszContentAux_le (positiveNNFunctional L)
      (K := ⟨univ, isCompact_univ⟩) (f := 1) (by simp)
  · apply le_csInf (rieszContentAux_image_nonempty _ _)
    rintro _ ⟨f, hf, rfl⟩
    apply (NNReal.coe_le_coe).mp
    change 1 ≤ L.1 (nnContinuousReal f)
    apply positive_unit_lower_bound L _ 1
    intro x
    exact_mod_cast hf x (mem_univ x)

@[simp] theorem positiveMeasure_univ (L : PositiveState K) : positiveMeasure L univ = 1 := by
  change (positiveMeasure L) (⟨univ, isCompact_univ⟩ : Compacts K) = 1
  rw [positiveMeasure_compact L ⟨univ, isCompact_univ⟩]
  change ((positiveContent L).toFun ⟨univ, isCompact_univ⟩ : ℝ≥0∞) = 1
  rw [positiveContent_univ, ENNReal.coe_one]

instance positiveMeasure_isProbability (L : PositiveState K) :
    IsProbabilityMeasure (positiveMeasure L) := ⟨positiveMeasure_univ L⟩

/-- This probability measure is constructed before the integral representation is proved. -/
def representingProbability (L : PositiveState K) : ProbabilityMeasure K :=
  ⟨positiveMeasure L, inferInstance⟩


/-- Compact lower bounds for the actual integral. -/
theorem positiveMeasure_integral_lower (L : PositiveState K)
    (S : Compacts K) (f : C(K, ℝ)) (hf : ∀ x, 0 ≤ f x)
    (hS : ∀ x ∈ S, 1 ≤ f x) :
    ((positiveContent L).toFun S : ℝ) ≤ ∫ x, f x ∂positiveMeasure L := by
  have hmeas : MeasurableSet (S : Set K) := S.isCompact.isClosed.measurableSet
  have hmono : (S : Set K).indicator (1 : K → ℝ) ≤ f := by
    intro x
    by_cases hx : x ∈ (S : Set K)
    · simpa [hx] using hS x hx
    · simpa [hx] using hf x
  have h := integral_mono ((integrable_const (1 : ℝ)).indicator hmeas)
    (continuous_integrable_probability (representingProbability L) f) hmono
  change (∫ x, (S : Set K).indicator (fun _ => (1 : ℝ)) x ∂positiveMeasure L) ≤
    (∫ x, f x ∂positiveMeasure L) at h
  rw [integral_indicator_const (1 : ℝ) hmeas, positiveMeasure_compact] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Compact upper bounds for the actual integral. -/
theorem positiveMeasure_integral_upper (L : PositiveState K)
    (S : Compacts K) (f : C(K, ℝ))
    (hf1 : ∀ x, f x ≤ 1) (hzero : ∀ x, x ∉ (S : Set K) → f x = 0) :
    (∫ x, f x ∂positiveMeasure L) ≤ ((positiveContent L).toFun S : ℝ) := by
  have hmeas : MeasurableSet (S : Set K) := S.isCompact.isClosed.measurableSet
  have hmono : f ≤ (S : Set K).indicator (1 : K → ℝ) := by
    intro x
    by_cases hx : x ∈ (S : Set K)
    · simpa [hx] using hf1 x
    · simp [hx, hzero x hx]
  have h := integral_mono (continuous_integrable_probability (representingProbability L) f)
    ((integrable_const (1 : ℝ)).indicator hmeas) hmono
  change (∫ x, f x ∂positiveMeasure L) ≤
    (∫ x, (S : Set K).indicator (fun _ => (1 : ℝ)) x ∂positiveMeasure L) at h
  rw [integral_indicator_const (1 : ℝ) hmeas, positiveMeasure_compact] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- Continuous ramps telescope exactly; their support is controlled by compact level sets. -/
def rieszRamp (f : C(K, ℝ)) (n i : ℕ) : C(K, ℝ) :=
  ⟨fun x => min ((n : ℝ) * f x) ((i : ℝ) + 1) - min ((n : ℝ) * f x) (i : ℝ),
    ((continuous_const.mul f.continuous).min continuous_const).sub
      ((continuous_const.mul f.continuous).min continuous_const)⟩

def rieszLevel (f : C(K, ℝ)) (n i : ℕ) : Compacts K :=
  ⟨{x | (i : ℝ) ≤ (n : ℝ) * f x},
    (isClosed_le continuous_const (continuous_const.mul f.continuous)).isCompact⟩

theorem rieszRamp_nonneg (f : C(K, ℝ)) (n i : ℕ) (x : K) :
    0 ≤ rieszRamp f n i x := by
  apply sub_nonneg.mpr
  exact min_le_min_left _ (by linarith)

theorem rieszRamp_le_one (f : C(K, ℝ)) (n i : ℕ) (x : K) :
    rieszRamp f n i x ≤ 1 := by
  change min ((n : ℝ) * f x) ((i : ℝ) + 1) - min ((n : ℝ) * f x) (i : ℝ) ≤ 1
  by_cases h : (n : ℝ) * f x ≤ i
  · rw [min_eq_left (h.trans (by linarith)), min_eq_left h]
    norm_num
  · rw [min_eq_right (le_of_not_ge h)]
    have hmin := min_le_right ((n : ℝ) * f x) ((i : ℝ) + 1)
    linarith only [hmin]

theorem rieszRamp_one (f : C(K, ℝ)) (n i : ℕ) (x : K)
    (hx : x ∈ rieszLevel f n (i + 1)) : rieszRamp f n i x = 1 := by
  change ((i + 1 : ℕ) : ℝ) ≤ (n : ℝ) * f x at hx
  have h : (i : ℝ) + 1 ≤ (n : ℝ) * f x := by simpa only [Nat.cast_add, Nat.cast_one] using hx
  change min ((n : ℝ) * f x) ((i : ℝ) + 1) - min ((n : ℝ) * f x) (i : ℝ) = 1
  rw [min_eq_right h, min_eq_right (show (i : ℝ) ≤ (n : ℝ) * f x by linarith only [h])]
  ring

theorem rieszRamp_zero (f : C(K, ℝ)) (n i : ℕ) (x : K)
    (hx : x ∉ rieszLevel f n i) : rieszRamp f n i x = 0 := by
  change ¬ (i : ℝ) ≤ (n : ℝ) * f x at hx
  have h : (n : ℝ) * f x ≤ i := (not_le.mp hx).le
  change min ((n : ℝ) * f x) ((i : ℝ) + 1) - min ((n : ℝ) * f x) (i : ℝ) = 0
  rw [min_eq_left (h.trans (by linarith)), min_eq_left h, sub_self]

theorem rieszRamp_sum (f : C(K, ℝ)) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∀ x, f x ≤ 1) (n : ℕ) :
    ∑ i ∈ Finset.range n, rieszRamp f n i = (n : ℝ) • f := by
  ext x
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul]
  have h := Finset.sum_range_sub (fun i : ℕ => min ((n : ℝ) * f x) (i : ℝ)) n
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
  change (∑ i ∈ Finset.range n,
    (min ((n : ℝ) * f x) ((i : ℝ) + 1) - min ((n : ℝ) * f x) (i : ℝ))) = _
  rw [h, min_eq_right (mul_nonneg (Nat.cast_nonneg n) (hf0 x)),
    min_eq_left (by nlinarith only [hf1 x, Nat.cast_nonneg (α := ℝ) n]), sub_zero]

/-- Both the given functional and its constructed integral lie between the same
lower and upper level-set sums. Their difference is at most one mesh step. -/
theorem riesz_unit_interval_error (L : PositiveState K) (f : C(K, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (n : ℕ) :
    |(n : ℝ) * (L.1 f - ∫ x, f x ∂positiveMeasure L)| ≤ 1 := by
  let a : ℕ → ℝ := fun i => (positiveContent L).toFun (rieszLevel f n i)
  have ha0 : a 0 = 1 := by
    have hlevel : rieszLevel f n 0 = ⟨univ, isCompact_univ⟩ := by
      apply Compacts.ext
      ext x
      simp only [rieszLevel, Compacts.coe_mk, mem_setOf_eq, Nat.cast_zero, mem_univ, iff_true]
      exact mul_nonneg (Nat.cast_nonneg n) (hf0 x)
    simp only [a, hlevel, positiveContent_univ, NNReal.coe_one]
  have han : 0 ≤ a n := NNReal.coe_nonneg _
  have htel := Finset.sum_range_sub' a n
  rw [Finset.sum_sub_distrib, ha0] at htel
  have hLlow : ∑ i ∈ Finset.range n, a (i + 1) ≤
      ∑ i ∈ Finset.range n, L.1 (rieszRamp f n i) := by
    apply Finset.sum_le_sum
    intro i _
    exact positiveContent_le L _ _ (rieszRamp_nonneg f n i)
      (fun x hx => (rieszRamp_one f n i x hx).ge)
  have hLup : (∑ i ∈ Finset.range n, L.1 (rieszRamp f n i)) ≤ ∑ i ∈ Finset.range n, a i := by
    apply Finset.sum_le_sum
    intro i _
    exact le_positiveContent L _ _ (rieszRamp_nonneg f n i) (rieszRamp_le_one f n i)
      (rieszRamp_zero f n i)
  have hIlow : ∑ i ∈ Finset.range n, a (i + 1) ≤
      ∑ i ∈ Finset.range n, (∫ x, rieszRamp f n i x ∂positiveMeasure L) := by
    apply Finset.sum_le_sum
    intro i _
    exact positiveMeasure_integral_lower L _ _ (rieszRamp_nonneg f n i)
      (fun x hx => (rieszRamp_one f n i x hx).ge)
  have hIup : (∑ i ∈ Finset.range n, (∫ x, rieszRamp f n i x ∂positiveMeasure L)) ≤
      ∑ i ∈ Finset.range n, a i := by
    apply Finset.sum_le_sum
    intro i _
    exact positiveMeasure_integral_upper L _ _ (rieszRamp_le_one f n i) (rieszRamp_zero f n i)
  have hLsum : (∑ i ∈ Finset.range n, L.1 (rieszRamp f n i)) = (n : ℝ) * L.1 f := by
    rw [← map_sum, rieszRamp_sum f hf0 hf1, _root_.map_smul, smul_eq_mul]
  have hIsum : (∑ i ∈ Finset.range n, (∫ x, rieszRamp f n i x ∂positiveMeasure L)) =
      (n : ℝ) * ∫ x, f x ∂positiveMeasure L := by
    rw [← integral_finset_sum]
    · have heq : (fun x => ∑ i ∈ Finset.range n, rieszRamp f n i x) = fun x => (n : ℝ) * f x := by
        funext x
        have h := congrArg (fun g : C(K, ℝ) => g x) (rieszRamp_sum f hf0 hf1 n)
        simpa only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul] using h
      rw [heq]
      exact integral_smul (n : ℝ) f
    · intro i _
      exact continuous_integrable_probability (representingProbability L) _
  rw [hLsum] at hLlow hLup
  rw [hIsum] at hIlow hIup
  apply abs_le.mpr
  constructor <;> nlinarith only [hLlow, hLup, hIlow, hIup, htel, han]


/-- Riesz equality first for continuous tests in the unit interval. -/
theorem positiveMeasure_integral_unit (L : PositiveState K) (f : C(K, ℝ))
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    L.1 f = ∫ x, f x ∂positiveMeasure L := by
  have hzero : |L.1 f - ∫ x, f x ∂positiveMeasure L| ≤ 0 := by
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    have h := riesz_unit_interval_error L f hf0 hf1 (n + 1)
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at h
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hdiv : |L.1 f - ∫ x, f x ∂positiveMeasure L| ≤ 1 / (n + 1 : ℕ) := by
      apply (le_div_iff hnpos).mpr
      simpa only [mul_comm] using h
    have hn' : (1 : ℝ) / (n + 1 : ℕ) < ε := by simpa only [Nat.cast_add, Nat.cast_one] using hn
    linarith only [hdiv, hn']
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

/-- Actual Bochner integral representation for every real continuous function. -/
theorem positiveMeasure_integral (L : PositiveState K) (f : C(K, ℝ)) :
    (∫ x, f x ∂positiveMeasure L) = L.1 f := by
  let c : ℝ := ‖f‖ + 1
  have hc : 0 < c := by dsimp [c]; linarith only [norm_nonneg f]
  have h2c : 0 < 2 * c := mul_pos (by norm_num) hc
  let g : C(K, ℝ) := (2 * c)⁻¹ • (f + ContinuousMap.const K c)
  have hg0 : ∀ x, 0 ≤ g x := by
    intro x
    change 0 ≤ (2 * c)⁻¹ * (f x + c)
    apply mul_nonneg (inv_nonneg.mpr h2c.le)
    have hx := f.neg_norm_le_apply x
    dsimp [c]
    linarith only [hx]
  have hg1 : ∀ x, g x ≤ 1 := by
    intro x
    change (2 * c)⁻¹ * (f x + c) ≤ 1
    rw [← div_eq_inv_mul]
    apply (div_le_iff h2c).mpr
    have hx := f.apply_le_norm x
    dsimp [c]
    linarith only [hx]
  have h := positiveMeasure_integral_unit L g hg0 hg1
  have heval : L.1 g = (2 * c)⁻¹ * (L.1 f + c) := by
    simp only [g, _root_.map_smul, map_add, positive_unit_const L.2, smul_eq_mul]
  have hint : (∫ x, g x ∂positiveMeasure L) =
      (2 * c)⁻¹ * ((∫ x, f x ∂positiveMeasure L) + c) := by
    change (∫ x, (2 * c)⁻¹ * (f x + c) ∂positiveMeasure L) = _
    have hfi : Integrable f (positiveMeasure L) :=
      continuous_integrable_probability (representingProbability L) f
    rw [integral_mul_left, integral_add hfi (integrable_const c)]
    simp only [integral_const, positiveMeasure_univ, ENNReal.one_toReal, smul_eq_mul, one_mul]
  rw [heval, hint] at h
  have hcancel := mul_left_cancel₀ (inv_ne_zero (ne_of_gt h2c)) h
  exact (add_right_cancel hcancel).symm

/-- The probability measure constructed from compact content represents the original state. -/
theorem probabilityFunctional_representing (L : PositiveState K) :
    probabilityFunctional (representingProbability L) = L := by
  apply Subtype.ext
  apply DFunLike.ext
  intro f
  exact positiveMeasure_integral L f

/-- Compact-space Riesz representation: positivity and normalization suffice. -/
theorem probability_functional_surjective :
    Function.Surjective (probabilityFunctional : ProbabilityMeasure K → PositiveState K) := by
  intro L
  exact ⟨representingProbability L, probabilityFunctional_representing L⟩

/-- The representing probability measure is unique under the same Borel separation
assumption used by the library's weak probability-measure topology. -/
theorem probability_representation_unique [HasOuterApproxClosed K] (L : PositiveState K) :
    ∃! ν : ProbabilityMeasure K, probabilityFunctional ν = L := by
  refine ⟨representingProbability L, probabilityFunctional_representing L, ?_⟩
  intro ν hν
  apply probability_functional_injective
  rw [hν, probabilityFunctional_representing]

end Measure

end BB
