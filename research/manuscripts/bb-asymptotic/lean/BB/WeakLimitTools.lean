import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Topology.Semicontinuous
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Tactic

/-!
# Weak limits with lower semicontinuous losses and negligible discontinuities

These are ordinary measure-theoretic consequences of Portmanteau.  They do
not assume the semiuniform conclusion or continuity of a map at its exceptional
null set.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]
  [OpensMeasurableSpace X]

theorem lowerSemicontinuous_real_lintegral_le_liminf
    {μ : Measure X} {μs : ℕ → Measure X} {f : X → ℝ}
    (hf : LowerSemicontinuous f) (hn : 0 ≤ f)
    (ho : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      atTop.liminf (fun i => ∫⁻ x, ENNReal.ofReal (f x) ∂μs i) := by
  simp_rw [lintegral_eq_lintegral_meas_lt _ (eventually_of_forall hn) hf.measurable.aemeasurable]
  calc
    ∫⁻ t : ℝ in Ioi 0, μ {x | t < f x}
      ≤ ∫⁻ t : ℝ in Ioi 0, atTop.liminf (fun i => μs i {x | t < f x}) :=
        lintegral_mono (fun t => ho _ (hf.isOpen_preimage t))
    _ ≤ atTop.liminf (fun i => ∫⁻ t : ℝ in Ioi 0, μs i {x | t < f x}) :=
        lintegral_liminf_le (fun _ => Antitone.measurable
          (fun _ _ hst => measure_mono (fun _ hx => lt_of_le_of_lt hst hx)))

theorem lowerSemicontinuous_lintegral_le_liminf
    {μ : Measure X} {μs : ℕ → Measure X} {q : X → ℝ≥0∞}
    (hq : LowerSemicontinuous q)
    (ho : ∀ G, IsOpen G → μ G ≤ atTop.liminf (fun i => μs i G)) :
    ∫⁻ x, q x ∂μ ≤ atTop.liminf (fun i => ∫⁻ x, q x ∂μs i) := by
  have ht (n : ℕ) : LowerSemicontinuous (fun x => ENNReal.truncateToReal n (q x)) :=
    (ENNReal.continuous_truncateToReal (by simp)).comp_lowerSemicontinuous hq
      (ENNReal.monotone_truncateToReal (by simp))
  have he (n : ℕ) (x : X) :
      ENNReal.ofReal (ENNReal.truncateToReal n (q x)) = min (n : ℝ≥0∞) (q x) := by
    exact ENNReal.ofReal_toReal (ne_top_of_le_ne_top (by simp) (min_le_left _ _))
  have hmin (n : ℕ) :
      ∫⁻ x, min (n : ℝ≥0∞) (q x) ∂μ ≤
        atTop.liminf (fun i => ∫⁻ x, q x ∂μs i) := by
    have h := lowerSemicontinuous_real_lintegral_le_liminf (ht n)
      (fun _ => ENNReal.truncateToReal_nonneg) ho
    simp_rw [he] at h
    exact h.trans (liminf_le_liminf (eventually_of_forall
      (fun i => lintegral_mono (fun x => min_le_right _ _))))
  have heq (x : X) : (⨆ n : ℕ, min (n : ℝ≥0∞) (q x)) = q x := by
    change (⨆ n : ℕ, (n : ℝ≥0∞) ⊓ q x) = q x
    rw [← iSup_inf_eq, ENNReal.iSup_natCast, top_inf_eq]
  calc
    ∫⁻ x, q x ∂μ = ∫⁻ x, ⨆ n : ℕ, min (n : ℝ≥0∞) (q x) ∂μ := by simp only [heq]
    _ = ⨆ n : ℕ, ∫⁻ x, min (n : ℝ≥0∞) (q x) ∂μ :=
      lintegral_iSup (fun _ => measurable_const.min hq.measurable)
        (fun _ _ h x => min_le_min (Nat.cast_le.mpr h) le_rfl)
    _ ≤ _ := iSup_le hmin

theorem probability_tendsto_of_closed_limsup
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hc : ∀ F, IsClosed F →
      atTop.limsup (fun i => (μs i : Measure X) F) ≤ (μ : Measure X) F) :
    Tendsto μs atTop (𝓝 μ) := by
  apply tendsto_of_forall_isOpen_le_liminf
  intro G hG
  have ho : (μ : Measure X) G ≤ atTop.liminf (fun i => (μs i : Measure X) G) :=
    le_measure_liminf_of_limsup_measure_compl_le hG.measurableSet (hc _ hG.isClosed_compl)
  have aux : ENNReal.ofNNReal (liminf (fun i => μs i G) atTop) =
      liminf (ENNReal.ofNNReal ∘ fun i => μs i G) atTop := by
    refine Monotone.map_liminf_of_continuousAt (F := atTop) ENNReal.coe_mono (μs · G) ?_ ?_ ?_
    · exact ENNReal.continuous_coe.continuousAt
    · use 1
      simp only [eventually_map, ProbabilityMeasure.apply_le_one, eventually_atTop, ge_iff_le,
        implies_true, forall_const, exists_const]
    · use 0
      simp only [zero_le, eventually_map, eventually_atTop, ge_iff_le, implies_true, forall_const,
        exists_const]
  apply ENNReal.coe_le_coe.mp
  rw [aux]
  convert ho using 1
  · exact ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure μ G
  · congr 1
    funext i
    exact ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure (μs i) G

theorem closure_preimage_subset_exception {Y : Type*} [TopologicalSpace Y]
    (T : X → Y) (D : Set X) (hT : ∀ x ∉ D, ContinuousAt T x)
    {F : Set Y} (hF : IsClosed F) : closure (T ⁻¹' F) ⊆ (T ⁻¹' F) ∪ D := by
  intro x hx
  by_cases hd : x ∈ D
  · exact Or.inr hd
  · apply Or.inl
    have hi := mem_closure_image (hT x hd) hx
    exact hF.closure_subset (closure_mono (image_preimage_subset T F) hi)

theorem probability_map_tendsto_of_null_discontinuities
    [HasOuterApproxClosed X]
    {μ : ProbabilityMeasure X} {μs : ℕ → ProbabilityMeasure X}
    (hlim : Tendsto μs atTop (𝓝 μ)) (T : X → X) (hm : Measurable T)
    (D : Set X) (hnull : (μ : Measure X) D = 0)
    (hT : ∀ x ∉ D, ContinuousAt T x) :
    Tendsto (fun i => (μs i).map hm.aemeasurable) atTop (𝓝 (μ.map hm.aemeasurable)) := by
  apply probability_tendsto_of_closed_limsup
  intro F hF
  simp only [ProbabilityMeasure.map_apply' _ _ hF.measurableSet]
  calc
    atTop.limsup (fun i => (μs i : Measure X) (T ⁻¹' F))
      ≤ atTop.limsup (fun i => (μs i : Measure X) (closure (T ⁻¹' F))) :=
        limsup_le_limsup (eventually_of_forall (fun _ => measure_mono subset_closure))
    _ ≤ (μ : Measure X) (closure (T ⁻¹' F)) :=
        ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hlim isClosed_closure
    _ ≤ (μ : Measure X) ((T ⁻¹' F) ∪ D) :=
        measure_mono (closure_preimage_subset_exception T D hT hF)
    _ ≤ (μ : Measure X) (T ⁻¹' F) + (μ : Measure X) D := measure_union_le _ _
    _ = (μ : Measure X) (T ⁻¹' F) := by rw [hnull, add_zero]

end BB
