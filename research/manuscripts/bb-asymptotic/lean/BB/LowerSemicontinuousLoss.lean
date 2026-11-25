import BB.EmpiricalMeasures
import BB.ProbabilityCompactness
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# The general compact semiuniform principle, in nonnegative loss coordinates

Long empirical segments have weakly convergent subsequences. Lower
semicontinuity bounds the limiting loss; finiteness makes the discontinuity
set null, and the proved empirical mapping theorem yields invariance.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {X : Type*} [MetricSpace X] [CompactSpace X]
  [MeasurableSpace X] [BorelSpace X]

theorem semicontinuous_loss_eventual_mean_lower
    (T : X → X) (hT : Measurable T) (D : Set X)
    (hc : ∀ x ∉ D, ContinuousAt T x) (q : X → ℝ≥0∞)
    (hq : LowerSemicontinuous q) (hD : ∀ x ∈ D, q x = ⊤)
    (γ : ℝ)
    (hinv : ∀ μ : ProbabilityMeasure X,
      MeasurePreserving T (μ : Measure X) (μ : Measure X) →
      (∫⁻ x, q x ∂(μ : Measure X)) ≠ ⊤ →
      ENNReal.ofReal γ ≤ ∫⁻ x, q x ∂(μ : Measure X))
    (η : ℝ) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : X,
      ENNReal.ofReal (γ - η) ≤
        ∫⁻ y, q y ∂(empiricalProbability T x (n + 1) (Nat.succ_pos n) : Measure X) := by
  by_cases hlow : γ - η ≤ 0
  · refine ⟨0, fun _ _ _ => ?_⟩
    rw [ENNReal.ofReal_eq_zero.mpr hlow]
    exact zero_le _
  have hpos : 0 < γ - η := lt_of_not_ge hlow
  by_contra hfail
  push_neg at hfail
  choose ns hlarge xs hbad using hfail
  let μs : ℕ → ProbabilityMeasure X := fun j =>
    empiricalProbability T (xs j) (ns j + 1) (Nat.succ_pos _)
  obtain ⟨μ, φ, hφ, hlim⟩ := SeqCompactSpace.tendsto_subseq μs
  have hbound : (∫⁻ x, q x ∂(μ : Measure X)) ≤ ENNReal.ofReal (γ - η) := by
    apply (lowerSemicontinuous_lintegral_le_liminf hq (fun G hG =>
      ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hG)).trans
    exact liminf_le_of_frequently_le'
      (eventually_of_forall (fun j => (hbad (φ j)).le)).frequently
  have hfin : (∫⁻ x, q x ∂(μ : Measure X)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hnull : (μ : Measure X) D = 0 := by
    apply compl_mem_ae_iff.mp
    filter_upwards [ae_lt_top hq.measurable hfin] with x hx
    intro hd
    exact hx.ne (hD x hd)
  have hnlim : Tendsto (fun j => ns j + 1) atTop atTop :=
    tendsto_atTop_mono (fun j => (hlarge j).trans (Nat.le_succ _)) tendsto_id
  have hpres : MeasurePreserving T (μ : Measure X) (μ : Measure X) :=
    empirical_limit_invariant T hT (xs ∘ φ) (fun j => ns (φ j) + 1)
      (fun _ => Nat.succ_pos _) (hnlim.comp hφ.tendsto_atTop) μ hlim D hnull hc
  have hcontra := (hinv μ hpres hfin).trans hbound
  have hr := (ENNReal.ofReal_le_ofReal_iff hpos.le).mp hcontra
  linarith

end BB
