import BB.HilbertProbabilityInvariant
import BB.HilbertRestrictedWeak

/-!
# Persistent deterministic support under ergodicity

Open-set evaluation is proved Borel from Portmanteau. A countable topological
base fixes the zero/nonzero mass pattern under ergodicity. No barycenter or
uncountable intersection is used.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology ENNReal

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]

lemma measureSupport_isClosed (ν : Measure K) : IsClosed (measureSupport ν) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  have hn : ¬ ∀ U : Set K, IsOpen U → x ∈ U → ν U ≠ 0 := hx
  push_neg at hn
  obtain ⟨U,hU,hxU,hzero⟩ := hn
  refine ⟨U,?_,hU,hxU⟩
  intro y hy hys
  exact hys U hU hy hzero

lemma mem_measureSupport_iff_countableBasis (ν : Measure K) (x : K) :
    x ∈ measureSupport ν ↔ ∀ U : countableBasis K, x ∈ (U : Set K) → ν (U : Set K) ≠ 0 := by
  constructor
  · intro hx U hxU
    exact hx U (isOpen_of_mem_countableBasis U.2) hxU
  · intro hx U hU hxU hzero
    obtain ⟨V,hV,hxV,hVU⟩ := (isBasis_countableBasis K).exists_subset_of_mem_open hxU hU
    exact hx ⟨V,hV⟩ hxV (measure_mono_null hVU hzero)

lemma measureSupport_eq_of_basis_null_iff (ν μ : Measure K)
    (h : ∀ U : countableBasis K, ν (U : Set K) = 0 ↔ μ (U : Set K) = 0) :
    measureSupport ν = measureSupport μ := by
  ext x
  simp only [mem_measureSupport_iff_countableBasis]
  exact forall_congr' (fun U => imp_congr_right (fun _ => not_congr (h U)))

lemma ae_mem_measureSupport (ν : Measure K) : ∀ᵐ x ∂ν, x ∈ measureSupport ν := by
  letI : Countable (countableBasis K) := (countable_countableBasis K).to_subtype
  have hU : ∀ U : countableBasis K, ∀ᵐ x ∂ν, ν (U : Set K) = 0 → x ∉ (U : Set K) := by
    intro U
    by_cases hz : ν (U : Set K) = 0
    · have hn : ∀ᵐ x ∂ν, x ∉ (U : Set K) := by
        apply ae_iff.mpr
        simpa only [not_not] using hz
      exact hn.mono (fun _ hx _ => hx)
    · exact eventually_of_forall (fun _ h => (hz h).elim)
  filter_upwards [ae_all_iff.mpr hU] with x hx
  apply (mem_measureSupport_iff_countableBasis ν x).mpr
  intro U hxU hzero
  exact hx U hzero hxU

lemma probability_measureSupport_nonempty (ν : ProbabilityMeasure K) :
    (measureSupport (ν : Measure K)).Nonempty := (ae_mem_measureSupport (ν : Measure K)).exists

lemma probability_integral_of_singleton_support (ν : ProbabilityMeasure K) (x : K)
    (hν : measureSupport (ν : Measure K) = {x}) (f : K → ℝ) :
    (∫ y, f y ∂(ν : Measure K)) = f x := by
  have hpoint : ∀ᵐ y ∂(ν : Measure K), y = x := by
    simpa only [hν,mem_singleton_iff] using ae_mem_measureSupport (ν : Measure K)
  calc
    (∫ y, f y ∂(ν : Measure K)) = ∫ _y : K, f x ∂(ν : Measure K) :=
      integral_congr_ae (hpoint.mono (fun _ hy => congrArg f hy))
    _ = f x := by simp

lemma probability_growth_zero_of_singleton_support (lam : C(K,ℝ)) (χ : ProbabilityState K)
    (x : K) (hlam : lam x ≠ 0)
    (hν : measureSupport (χ.1 : Measure K) = {x})
    (hζ : measureSupport (χ.2 : Measure K) = {x}) : probabilityGrowth lam χ = 0 := by
  have hmean : probabilityMean lam χ = lam x := probability_integral_of_singleton_support χ.2 x hζ lam
  unfold probabilityGrowth probabilityGrowthSq
  rw [probability_integral_of_singleton_support χ.1 x hν, hmean, div_self hlam,sub_self,zero_pow (by decide : 2 ≠ 0),Real.sqrt_zero]

lemma probability_open_mass_lowerSemicontinuous (U : Set K) (hU : IsOpen U) :
    LowerSemicontinuous (fun ν : ProbabilityMeasure K => (ν : Measure K) U) := by
  apply lowerSemicontinuous_iff_le_liminf.mpr
  intro ν
  exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hU

section CountablePattern
variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- An ergodic law fixes the complete countable pattern of persistent zero
observables. A representative may be chosen inside any prescribed full set. -/
lemma ergodic_countable_zero_pattern (μ : Measure X) [IsProbabilityMeasure μ]
    (T : X → X) (hT : Ergodic T μ) (b : ι → X → ℝ≥0∞)
    (hb : ∀ i, Measurable (b i))
    (hpersist : ∀ i x, b i x = 0 → b i (T x) = 0)
    (P : X → Prop) (hP : ∀ᵐ x ∂μ, P x) :
    ∃ x₀ : X, P x₀ ∧ ∀ᵐ x ∂μ, ∀ i, b i x = 0 ↔ b i x₀ = 0 := by
  classical
  have hc : ∀ i, ∃ p : Prop, ∀ᵐ x ∂μ, b i x = 0 ↔ p := by
    intro i
    let A : Set X := {x | b i x = 0}
    have hA : MeasurableSet A := (hb i) (measurableSet_singleton 0)
    have hforward : A ⊆ T ⁻¹' A := fun x hx => hpersist i x hx
    have hinv := invariant_event_of_forward_closed μ T hT.toMeasurePreserving A hA hforward
    rcases hT.quasiErgodic.ae_empty_or_univ' hA hinv.symm with hzero | hfull
    · refine ⟨False,?_⟩
      exact (eventuallyEq_empty.mp hzero).mono (fun x hx => iff_false_intro hx)
    · refine ⟨True,?_⟩
      have hmem : ∀ᵐ x ∂μ, x ∈ A := eventuallyEq_univ.mp hfull
      exact hmem.mono (fun x hx => iff_true_intro hx)
  choose p hp using hc
  have hall := ae_all_iff.mpr hp
  obtain ⟨x₀,hx₀,hPx₀⟩ := (hall.and hP).exists
  refine ⟨x₀,hPx₀,?_⟩
  exact hall.mono (fun x hx i => (hx i).trans (hx₀ i).symm)

/-- Countably many full-measure preimages produce a genuinely forward-invariant
Borel core, rather than only an almost invariant set. -/
def forwardFullCore (T : X → X) (Y : Set X) : Set X := {x | ∀ n : ℕ, T^[n] x ∈ Y}

lemma forwardFullCore_measurable (T : X → X) (hT : Measurable T) (Y : Set X) (hY : MeasurableSet Y) :
    MeasurableSet (forwardFullCore T Y) := by
  simp only [forwardFullCore,setOf_forall]
  exact MeasurableSet.iInter (fun n => hY.preimage (hT.iterate n))

lemma forwardFullCore_full (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (Y : Set X) (hY : ∀ᵐ x ∂μ, x ∈ Y) : ∀ᵐ x ∂μ, x ∈ forwardFullCore T Y := by
  apply ae_all_iff.mpr
  intro n
  exact (hT.iterate n).quasiMeasurePreserving.ae hY

lemma forwardFullCore_subset (T : X → X) (Y : Set X) : forwardFullCore T Y ⊆ Y := by
  intro x hx
  exact hx 0

lemma forwardFullCore_forward (T : X → X) (Y : Set X) : T '' forwardFullCore T Y ⊆ forwardFullCore T Y := by
  rintro _ ⟨x,hx,rfl⟩ n
  simpa only [Function.iterate_succ_apply] using hx (n+1)

end CountablePattern
section ProbabilitySupport
variable [MeasurableSpace (ProbabilityState K)] [BorelSpace (ProbabilityState K)]

def firstOpenMass (U : Set K) : Cemetery (ProbabilityState K) → ℝ≥0∞ :=
  Sum.elim (fun χ => (χ.1 : Measure K) U) (fun _ => 0)

def secondOpenMass (U : Set K) : Cemetery (ProbabilityState K) → ℝ≥0∞ :=
  Sum.elim (fun χ => (χ.2 : Measure K) U) (fun _ => 0)

lemma firstOpenMass_measurable (U : Set K) (hU : IsOpen U) : Measurable (firstOpenMass U) :=
  ((probability_open_mass_lowerSemicontinuous U hU).comp_continuous continuous_fst).measurable.sumElim measurable_const

lemma secondOpenMass_measurable (U : Set K) (hU : IsOpen U) : Measurable (secondOpenMass U) :=
  ((probability_open_mass_lowerSemicontinuous U hU).comp_continuous continuous_snd).measurable.sumElim measurable_const

lemma probability_map_first_absolutelyContinuous (lam : C(K,ℝ)) (χ : ProbabilityState K) :
    ((probabilityMap lam χ).1 : Measure K) ≪ (χ.1 : Measure K) := by
  by_cases h : 0 < probabilityGrowthSq lam χ
  · rw [probabilityMap,dif_pos h]
    exact normalizedReweight_absolutelyContinuous (χ.1 : Measure K) _
  · rw [probabilityMap,dif_neg h]

lemma firstOpenMass_zero_persistent (lam : C(K,ℝ)) (U : Set K)
    (χ : Cemetery (ProbabilityState K)) (hzero : firstOpenMass U χ = 0) :
    firstOpenMass U (killedMap (probabilityMap lam) (probabilityGrowth lam) χ) = 0 := by
  cases χ with
  | inl χ =>
    by_cases hreg : 0 < probabilityGrowth lam χ
    · rw [killedMap_regular _ _ _ hreg]
      exact probability_map_first_absolutelyContinuous lam χ hzero
    · rw [killedMap_singular _ _ _ hreg]
      rfl
  | inr u => cases u; exact hzero

lemma secondOpenMass_shift (lam : C(K,ℝ)) (U : Set K)
    (χ : Cemetery (ProbabilityState K)) (hreg : 0 < killedMultiplier (probabilityGrowth lam) χ) :
    secondOpenMass U (killedMap (probabilityMap lam) (probabilityGrowth lam) χ) = firstOpenMass U χ := by
  cases χ with
  | inl χ =>
    change 0 < probabilityGrowth lam χ at hreg
    rw [killedMap_regular _ _ _ hreg]
    have hR : 0 < probabilityGrowthSq lam χ := Real.sqrt_pos.mp hreg
    change ((probabilityMap lam χ).2 : Measure K) U = (χ.1 : Measure K) U
    rw [probabilityMap,dif_pos hR]
  | inr u => exact (lt_irrefl 0 hreg).elim

def zeroPatternSet {X ι : Type*} (b : ι → X → ℝ≥0∞) (x₀ : X) : Set X :=
  {x | ∀ i, b i x = 0 ↔ b i x₀ = 0}

lemma zeroPatternSet_measurable {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (b : ι → X → ℝ≥0∞) (hb : ∀ i, Measurable (b i)) (x₀ : X) :
    MeasurableSet (zeroPatternSet b x₀) := by
  simp only [zeroPatternSet,setOf_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases h : b i x₀ = 0
  · simp only [h,iff_true]
    exact (hb i) (measurableSet_singleton 0)
  · simp only [h,iff_false]
    exact ((hb i) (measurableSet_singleton 0)).compl

lemma zeroPattern_shift_ae {X ι : Type*} [MeasurableSpace X] [Countable ι]
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (b d : ι → X → ℝ≥0∞) (hd : ∀ i, Measurable (d i)) (x₀ : X)
    (hpattern : ∀ᵐ x ∂μ, ∀ i, b i x = 0 ↔ b i x₀ = 0)
    (hshift : ∀ᵐ x ∂μ, ∀ i, d i (T x) = b i x) :
    ∀ᵐ x ∂μ, ∀ i, d i x = 0 ↔ b i x₀ = 0 := by
  apply ae_all_iff.mpr
  intro i
  have hmeas : MeasurableSet {x | d i x = 0 ↔ b i x₀ = 0} := by
    by_cases h : b i x₀ = 0
    · simp only [h,iff_true]; exact (hd i) (measurableSet_singleton 0)
    · simp only [h,iff_false]; exact ((hd i) (measurableSet_singleton 0)).compl
  have hpull : ∀ᵐ x ∂μ, d i (T x) = 0 ↔ b i x₀ = 0 := by
    filter_upwards [hpattern,hshift] with x hx hs
    rw [hs i]
    exact hx i
  have hmap := (ae_map_iff hT.measurable.aemeasurable hmeas).mpr hpull
  rwa [hT.map_eq] at hmap

/-- The original persistent-support statement, with an explicitly constructed
Borel full forward-invariant core and a compact non-singleton common support.
The law is on the actual isolated-terminal weak probability-measure state
space. The representative defining the support is selected in a regular full
set, not postulated. -/
theorem probability_hilbert_persistent_support (lam : C(K,ℝ)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ x, a ≤ lam x ∧ lam x ≤ b)
    (μ : Measure (Cemetery (ProbabilityState K))) [IsProbabilityMeasure μ]
    (hT : Ergodic (killedMap (probabilityMap lam) (probabilityGrowth lam)) μ)
    (hfinite : extendedLogIntegral (killedMultiplier (probabilityGrowth lam)) (Real.log (1+b/a)) μ ≠ ⊥) :
    ∃ S : Set K, IsCompact S ∧ S.Nontrivial ∧
      ∃ Y : Set (Cemetery (ProbabilityState K)), MeasurableSet Y ∧
        (∀ᵐ χ ∂μ, χ ∈ Y) ∧
        (killedMap (probabilityMap lam) (probabilityGrowth lam)) '' Y ⊆ Y ∧
        ∀ χ ∈ Y, ∃ ξ : ProbabilityState K, χ = Sum.inl ξ ∧
          measureSupport (ξ.1 : Measure K) = S ∧ measureSupport (ξ.2 : Measure K) = S ∧
          0 < probabilityGrowth lam ξ := by
  classical
  letI : Countable (countableBasis K) := (countable_countableBasis K).to_subtype
  let T := killedMap (probabilityMap lam) (probabilityGrowth lam)
  let r := killedMultiplier (probabilityGrowth lam)
  let b₁ : countableBasis K → Cemetery (ProbabilityState K) → ℝ≥0∞ := fun U => firstOpenMass U
  let b₂ : countableBasis K → Cemetery (ProbabilityState K) → ℝ≥0∞ := fun U => secondOpenMass U
  have hb₁ : ∀ U, Measurable (b₁ U) := fun U => firstOpenMass_measurable U (isOpen_of_mem_countableBasis U.2)
  have hb₂ : ∀ U, Measurable (b₂ U) := fun U => secondOpenMass_measurable U (isOpen_of_mem_countableBasis U.2)
  have hrmeas : Measurable r := killedMultiplier_measurable _
    (probability_growth_continuous lam a ha (fun x => (hlam x).1)).measurable
  have hupper : ∀ χ, 0 < r χ → Real.log (r χ) ≤ Real.log (1+b/a) := by
    intro χ hχ
    cases χ with
    | inl ξ => exact Real.log_le_log hχ (probability_growth_bound lam a b ha hab hlam ξ)
    | inr u => exact (lt_irrefl 0 hχ).elim
  have hregular := (extendedLogIntegral_finite_reduction r hrmeas _ hupper μ hfinite).1
  obtain ⟨χ₀,hχ₀,hpattern⟩ := ergodic_countable_zero_pattern μ T hT b₁ hb₁
    (fun U χ hχ => firstOpenMass_zero_persistent lam U χ hχ) (fun χ => 0 < r χ) hregular
  have hsecond := zeroPattern_shift_ae μ T hT.toMeasurePreserving b₁ b₂ hb₂ χ₀ hpattern
    (hregular.mono (fun χ hχ U => secondOpenMass_shift lam U χ hχ))
  cases χ₀ with
  | inr u => exact (lt_irrefl 0 hχ₀).elim
  | inl ξ₀ =>
    let S := measureSupport (ξ₀.1 : Measure K)
    let A₁ := zeroPatternSet b₁ (Sum.inl ξ₀)
    let A₂ : Set (Cemetery (ProbabilityState K)) :=
      {χ | ∀ U, b₂ U χ = 0 ↔ b₁ U (Sum.inl ξ₀) = 0}
    have hA₁ : MeasurableSet A₁ := zeroPatternSet_measurable b₁ hb₁ _
    have hA₂ : MeasurableSet A₂ := by
      simp only [A₂,setOf_forall]
      apply MeasurableSet.iInter
      intro U
      by_cases h : b₁ U (Sum.inl ξ₀) = 0
      · simp only [h,iff_true]; exact (hb₂ U) (measurableSet_singleton 0)
      · simp only [h,iff_false]; exact ((hb₂ U) (measurableSet_singleton 0)).compl
    let Z : Set (Cemetery (ProbabilityState K)) := {χ | 0 < r χ} ∩ A₁ ∩ A₂
    have hZ : MeasurableSet Z :=
      ((measurableSet_lt measurable_const hrmeas).inter hA₁).inter hA₂
    have hZfull : ∀ᵐ χ ∂μ, χ ∈ Z := by
      filter_upwards [hregular,hpattern,hsecond] with χ hχ hp hs
      exact ⟨⟨hχ,hp⟩,hs⟩
    have hgood : ∀ χ ∈ Z, ∃ ξ : ProbabilityState K, χ = Sum.inl ξ ∧
        measureSupport (ξ.1 : Measure K) = S ∧ measureSupport (ξ.2 : Measure K) = S ∧
        0 < probabilityGrowth lam ξ := by
      intro χ hχ
      cases χ with
      | inr u =>
        have hfalse : 0 < (0 : ℝ) := hχ.1.1
        exact (lt_irrefl 0 hfalse).elim
      | inl ξ =>
        refine ⟨ξ,rfl,?_,?_,hχ.1.1⟩
        · exact measureSupport_eq_of_basis_null_iff _ _ hχ.1.2
        · exact measureSupport_eq_of_basis_null_iff _ _ hχ.2
    have hScompact : IsCompact S := (measureSupport_isClosed _).isCompact
    have hSnontrivial : S.Nontrivial := by
      by_contra hn
      obtain ⟨x,hx⟩ := probability_measureSupport_nonempty ξ₀.1
      have hsing : S = {x} := (Set.not_nontrivial_iff.mp hn).eq_singleton_of_mem hx
      obtain ⟨χ,hχ⟩ := hZfull.exists
      obtain ⟨ξ,_heq,hν,hζ,hR⟩ := hgood χ hχ
      have hz := probability_growth_zero_of_singleton_support lam ξ x
        (ha.trans_le (hlam x).1).ne' (hν.trans hsing) (hζ.trans hsing)
      rw [hz] at hR
      exact lt_irrefl 0 hR
    refine ⟨S,hScompact,hSnontrivial,forwardFullCore T Z,
      forwardFullCore_measurable T hT.measurable Z hZ,
      forwardFullCore_full μ T hT.toMeasurePreserving Z hZfull,
      forwardFullCore_forward T Z,?_⟩
    intro χ hχ
    exact hgood χ (forwardFullCore_subset T Z hχ)

end ProbabilitySupport
end BB
