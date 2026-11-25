import BB.BorelFunctionalCalculus

/-!
# Strongly countably additive orthogonal projection-valued measures

The construction theorem below turns an actual family of finite scalar measures
and its actual spectral projections into a projection-valued measure. All
operator algebra and strong countable additivity are proved from the scalar
identities. The next module instantiates these data for the constructed scalar
spectral measures of a bounded symmetric operator.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology BigOperators
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable (K E : Type*) [MeasurableSpace K] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- A genuine real orthogonal projection-valued measure, with countable
additivity in the strong operator topology. -/
structure ProjectionValuedMeasure where
  map : ∀ s : Set K, MeasurableSet s → E →L[ℝ] E
  empty : map ∅ MeasurableSet.empty = 0
  univ : map univ MeasurableSet.univ = ContinuousLinearMap.id ℝ E
  symmetric : ∀ s hs, (map s hs).toLinearMap.IsSymmetric
  disjoint_union : ∀ s t hs ht, Disjoint s t →
    map (s ∪ t) (hs.union ht) = map s hs + map t ht
  inter : ∀ s t hs ht, (map s hs).comp (map t ht) = map (s ∩ t) (hs.inter ht)
  countably_additive : ∀ (s : ℕ → Set K) (hs : ∀ n, MeasurableSet (s n)),
    Pairwise (fun n m => Disjoint (s n) (s m)) → ∀ x : E,
    Tendsto (fun n => ∑ i ∈ Finset.range n, map (s i) (hs i) x) atTop
      (𝓝 (map (⋃ i, s i) (MeasurableSet.iUnion hs) x))

variable {K E}

namespace ProjectionValuedMeasure

theorem idempotent (P : ProjectionValuedMeasure K E) (s : Set K) (hs : MeasurableSet s) :
    (P.map s hs).comp (P.map s hs) = P.map s hs := by
  simpa only [inter_self] using P.inter s s hs hs

theorem commute (P : ProjectionValuedMeasure K E) (s t : Set K)
    (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (P.map s hs).comp (P.map t ht) = (P.map t ht).comp (P.map s hs) := by
  rw [P.inter, P.inter]
  congr 1
  exact inter_comm _ _

theorem disjoint_mul (P : ProjectionValuedMeasure K E) (s t : Set K)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hst : Disjoint s t) :
    (P.map s hs).comp (P.map t ht) = 0 := by
  rw [P.inter]
  simpa only [disjoint_iff_inter_eq_empty.mp hst] using P.empty

/-- Push a projection-valued measure forward by a measurable map. -/
def mapMeasurable {L : Type*} [MeasurableSpace L]
    (P : ProjectionValuedMeasure K E) (f : K → L) (hf : Measurable f) :
    ProjectionValuedMeasure L E where
  map s hs := P.map (f ⁻¹' s) (hs.preimage hf)
  empty := by simpa only [preimage_empty] using P.empty
  univ := by simpa only [preimage_univ] using P.univ
  symmetric s hs := P.symmetric _ _
  disjoint_union s t hs ht hd := P.disjoint_union _ _ _ _ (hd.preimage f)
  inter s t hs ht := P.inter _ _ _ _
  countably_additive s hs hd x := by
    have hd' : Pairwise (fun n m => Disjoint (f ⁻¹' s n) (f ⁻¹' s m)) :=
      fun n m hnm => (hd hnm).preimage f
    simpa only [preimage_iUnion] using
      P.countably_additive (fun n => f ⁻¹' s n) (fun n => (hs n).preimage hf) hd' x

end ProjectionValuedMeasure

section Construction

variable (P : ∀ s : Set K, MeasurableSet s → E →L[ℝ] E)
  (μ : E → FiniteMeasure K)
  (hself : ∀ s hs, (P s hs).toLinearMap.IsSymmetric)
  (hdiag : ∀ s hs x, ⟪P s hs x, x⟫ = ((μ x : Measure K) s).toReal)
  (hnorm : ∀ s hs x, ‖P s hs x‖^2 = ((μ x : Measure K) s).toReal)
  (hmass : ∀ x, (μ x : Measure K) univ = ENNReal.ofReal (‖x‖^2))
  (hrestrict : ∀ s hs x, (μ (P s hs x) : Measure K) = (μ x : Measure K).restrict s)

theorem projection_family_empty : P ∅ MeasurableSet.empty = 0 := by
  ext x
  have hn := hnorm ∅ MeasurableSet.empty x
  simp only [measure_empty, ENNReal.zero_toReal] at hn
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem projection_family_univ : P univ MeasurableSet.univ = ContinuousLinearMap.id ℝ E := by
  apply symmetric_operator_eq_of_diagonal _ _ (hself _ _) (by
    intro x y
    rfl)
  intro x
  rw [hdiag, hmass, ENNReal.toReal_ofReal (sq_nonneg _)]
  simp only [ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq]

theorem projection_family_union (s t : Set K) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) :
    P (s ∪ t) (hs.union ht) = P s hs + P t ht := by
  apply symmetric_operator_eq_of_diagonal _ _ (hself _ _) (by
    intro x y
    change ⟪P s hs x + P t ht x, y⟫ = ⟪x, P s hs y + P t ht y⟫
    rw [inner_add_left, inner_add_right]
    exact congrArg₂ (· + ·) (hself s hs x y) (hself t ht x y))
  intro x
  change ⟪P (s ∪ t) _ x, x⟫ = ⟪P s hs x + P t ht x, x⟫
  rw [inner_add_left, hdiag, hdiag, hdiag, measure_union hst ht,
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]

theorem projection_family_disjoint_mul (s t : Set K) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hst : Disjoint s t) :
    (P s hs).comp (P t ht) = 0 := by
  ext x
  have hn := hnorm s hs (P t ht x)
  rw [hrestrict t ht x, Measure.restrict_apply hs,
    disjoint_iff_inter_eq_empty.mp hst, measure_empty, ENNReal.zero_toReal] at hn
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

theorem projection_family_subset_mul (s t : Set K) (hs : MeasurableSet s)
    (ht : MeasurableSet t) (hts : t ⊆ s) :
    (P s hs).comp (P t ht) = P t ht := by
  have hu := projection_family_union (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) s sᶜ hs hs.compl disjoint_compl_right
  have hid := projection_family_univ (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (hmass := hmass)
  have hz := projection_family_disjoint_mul (P := P) (μ := μ) (hnorm := hnorm) (hrestrict := hrestrict) sᶜ t hs.compl ht (by
    rw [disjoint_left]
    intro z hz ht
    exact hz (hts ht))
  have hsum : P s hs + P sᶜ hs.compl = ContinuousLinearMap.id ℝ E := by
    have hu' : ContinuousLinearMap.id ℝ E = P s hs + P sᶜ hs.compl := by
      simpa only [union_compl_self, hid] using hu
    exact hu'.symm
  ext x
  have hx := congrArg (fun L : E →L[ℝ] E => L (P t ht x)) hsum
  have hz' := congrArg (fun L : E →L[ℝ] E => L x) hz
  change P s hs (P t ht x) = P t ht x
  change P sᶜ hs.compl (P t ht x) = 0 at hz'
  change P s hs (P t ht x) + P sᶜ hs.compl (P t ht x) = P t ht x at hx
  simpa only [hz', add_zero] using hx

theorem projection_family_inter (s t : Set K) (hs : MeasurableSet s)
    (ht : MeasurableSet t) :
    (P s hs).comp (P t ht) = P (s ∩ t) (hs.inter ht) := by
  have hdecomp : (s ∩ t) ∪ (t \ s) = t := by ext x; simp only [mem_union,mem_inter_iff,mem_diff]; tauto
  have hdis : Disjoint (s ∩ t) (t \ s) := by
    rw [disjoint_left]
    intro x hx hy
    exact hy.2 hx.1
  have hsum := projection_family_union (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (s ∩ t) (t \ s)
    (hs.inter ht) (ht.diff hs) hdis
  have hone := projection_family_subset_mul (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (hnorm := hnorm) (hmass := hmass) (hrestrict := hrestrict)
    s (s ∩ t) hs (hs.inter ht) (inter_subset_left s t)
  have hzero := projection_family_disjoint_mul (P := P) (μ := μ) (hnorm := hnorm) (hrestrict := hrestrict)
    s (t \ s) hs (ht.diff hs) (by
      rw [disjoint_left]
      intro x hx hy
      exact hy.2 hx)
  have hsum' : P t ht = P (s ∩ t) (hs.inter ht) + P (t \ s) (ht.diff hs) := by
    simpa only [hdecomp] using hsum
  rw [hsum', ContinuousLinearMap.comp_add, hone, hzero, add_zero]

theorem projection_family_finset_union (s : ℕ → Set K) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (fun n m => Disjoint (s n) (s m))) (F : Finset ℕ) :
    P (⋃ i ∈ F, s i) (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i) = ∑ i ∈ F, P (s i) (hs i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simpa using projection_family_empty (P := P) (μ := μ) (hnorm := hnorm)
  | @insert i F hi ih =>
    have hd' : Disjoint (s i) (⋃ j ∈ F, s j) := by
      simp only [disjoint_iUnion_right]
      intro j hj
      exact hd (by intro heq; exact hi (heq ▸ hj))
    have hu := projection_family_union (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (s i) (⋃ j ∈ F, s j)
      (hs i) (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i) hd'
    simpa only [Finset.set_biUnion_insert, Finset.sum_insert hi, ih] using hu

theorem projection_family_countably_additive (s : ℕ → Set K) (hs : ∀ n, MeasurableSet (s n))
    (hd : Pairwise (fun n m => Disjoint (s n) (s m))) (x : E) :
    Tendsto (fun n => ∑ i ∈ Finset.range n, P (s i) (hs i) x) atTop
      (𝓝 (P (⋃ i, s i) (MeasurableSet.iUnion hs) x)) := by
  let tails : ℕ → Set K := fun n => ⋃ i ≥ n, s i
  have htails (n : ℕ) : MeasurableSet (tails n) := by dsimp [tails]; measurability
  have htend : Tendsto (fun n => ((μ x : Measure K) (tails n)).toReal) atTop (𝓝 0) := by
    have h := tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint (μ := (μ x : Measure K)) hs hd
    simpa only [ENNReal.zero_toReal] using (ENNReal.continuousAt_toReal (by simp)).tendsto.comp h
  have hnormtend : Tendsto (fun n => ‖P (tails n) (htails n) x‖) atTop (𝓝 0) := by
    have h := (Real.continuous_sqrt.tendsto 0).comp htend
    have heq (n : ℕ) : Real.sqrt (((μ x : Measure K) (tails n)).toReal) = ‖P (tails n) (htails n) x‖ := by
      rw [← hnorm (tails n) (htails n) x, Real.sqrt_sq (norm_nonneg _)]
    change Tendsto (fun n => Real.sqrt (((μ x : Measure K) (tails n)).toReal)) atTop (𝓝 (Real.sqrt 0)) at h
    simpa only [heq, Real.sqrt_zero] using h
  have htailzero : Tendsto (fun n => P (tails n) (htails n) x) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr hnormtend
  have hformula (n : ℕ) :
      ∑ i ∈ Finset.range n, P (s i) (hs i) x =
        P (⋃ i, s i) (MeasurableSet.iUnion hs) x - P (tails n) (htails n) x := by
    have hsets : (⋃ i ∈ Finset.range n, s i) ∪ tails n = ⋃ i, s i := by
      ext z
      simp only [mem_union, mem_iUnion, Finset.mem_range, exists_prop, tails, ge_iff_le]
      constructor
      · rintro (⟨i,_hi,hzi⟩ | ⟨i,_hi,hzi⟩) <;> exact ⟨i,hzi⟩
      · rintro ⟨i,hi⟩
        rcases lt_or_ge i n with hin | hni
        · exact Or.inl ⟨i,hin,hi⟩
        · exact Or.inr ⟨i,hni,hi⟩
    have hdis : Disjoint (⋃ i ∈ Finset.range n, s i) (tails n) := by
      simp only [tails, disjoint_iUnion_left, disjoint_iUnion_right]
      intro i hi j hj
      exact hd (ne_of_lt (lt_of_lt_of_le (Finset.mem_range.mp hj) hi))
    have hu := projection_family_union (P := P) (μ := μ) (hself := hself) (hdiag := hdiag)
      (⋃ i ∈ Finset.range n, s i) (tails n) (MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun _ => hs i) (htails n) hdis
    have hu' : P (⋃ i, s i) (MeasurableSet.iUnion hs) =
        (∑ i ∈ Finset.range n, P (s i) (hs i)) + P (tails n) (htails n) := by
      simpa only [hsets, projection_family_finset_union (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (hnorm := hnorm) s hs hd] using hu
    apply eq_sub_iff_add_eq.mpr
    calc
      (∑ i ∈ Finset.range n, P (s i) (hs i) x) + P (tails n) (htails n) x =
          ((∑ i ∈ Finset.range n, P (s i) (hs i)) + P (tails n) (htails n)) x := by
        rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply]
      _ = P (⋃ i, s i) (MeasurableSet.iUnion hs) x :=
        congrArg (fun L : E →L[ℝ] E => L x) hu'.symm
  simpa only [hformula, sub_zero] using tendsto_const_nhds.sub htailzero

/-- All fields of the projection-valued measure are theorems obtained from the
scalar spectral measure identities. -/
def projectionValuedMeasureOfScalar : ProjectionValuedMeasure K E where
  map := P
  empty := projection_family_empty (P := P) (μ := μ) (hnorm := hnorm)
  univ := projection_family_univ (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (hmass := hmass)
  symmetric := hself
  disjoint_union := projection_family_union (P := P) (μ := μ) (hself := hself) (hdiag := hdiag)
  inter := projection_family_inter (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (hnorm := hnorm) (hmass := hmass) (hrestrict := hrestrict)
  countably_additive := projection_family_countably_additive (P := P) (μ := μ) (hself := hself) (hdiag := hdiag) (hnorm := hnorm)

end Construction
end BB
