import BB.Cemetery
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.MetricSpace.Gluing

/-!
# Topology of the isolated terminal state

The source compactification uses the disjoint-sum topology.  Its multiplier
is continuous, its extended logarithm is upper semicontinuous, and the killed
map is continuous at every regular point and at the isolated terminal point.
Thus any discontinuity belongs to the singular set, where the logarithm is
literally minus infinity.
-/

noncomputable section
namespace BB
open Filter Set
open scoped Topology

theorem extendedLog_lt_real_iff (r t : ℝ) :
    extendedLog r < (t : EReal) ↔ r < Real.exp t := by
  by_cases hr : 0 < r
  · simp only [extendedLog, if_pos hr, EReal.coe_lt_coe_iff]
    exact Real.log_lt_iff_lt_exp hr
  · simp only [extendedLog, if_neg hr, EReal.bot_lt_coe, true_iff]
    exact (not_lt.mp hr).trans_lt (Real.exp_pos t)

theorem extendedLog_upperSemicontinuous : UpperSemicontinuous extendedLog := by
  apply upperSemicontinuous_iff_isOpen_preimage.mpr
  intro y
  induction y with
  | h_bot => simp
  | h_real t =>
    have he : extendedLog ⁻¹' Iio (t : EReal) = Iio (Real.exp t) := by
      ext r
      exact extendedLog_lt_real_iff r t
    rw [he]
    exact isOpen_Iio
  | h_top =>
    have he : extendedLog ⁻¹' Iio (⊤ : EReal) = univ := by
      ext r
      simp only [mem_preimage, mem_Iio, mem_univ, iff_true]
      by_cases hr : 0 < r <;> simp [extendedLog, hr]
    rw [he]
    exact isOpen_univ

variable {X : Type*} [TopologicalSpace X]

theorem killedMultiplier_continuous (r : X → ℝ) (hr : Continuous r) :
    Continuous (killedMultiplier r) := hr.sum_elim continuous_const

theorem killedLog_upperSemicontinuous (r : X → ℝ) (hr : Continuous r) :
    UpperSemicontinuous (fun s : Cemetery X => extendedLog (killedMultiplier r s)) :=
  extendedLog_upperSemicontinuous.comp_continuous (killedMultiplier_continuous r hr)

theorem killedMap_continuousAt_regular (T : X → X) (r : X → ℝ)
    (hr : Continuous r) (x : X) (hx : 0 < r x) (hT : ContinuousAt T x) :
    ContinuousAt (killedMap T r) (Sum.inl x) := by
  change Tendsto (killedMap T r) (𝓝 (Sum.inl x)) (𝓝 (killedMap T r (Sum.inl x)))
  rw [nhds_inl, tendsto_map'_iff, killedMap_regular T r x hx]
  have h : ContinuousAt (fun y => (Sum.inl (T y) : Cemetery X)) x :=
    continuous_inl.continuousAt.comp hT
  apply h.tendsto.congr'
  filter_upwards [(isOpen_lt continuous_const hr).mem_nhds hx] with y hy
  exact (killedMap_regular T r y hy).symm

theorem killedMap_continuousAt_point (T : X → X) (r : X → ℝ) :
    ContinuousAt (killedMap T r) (cemeteryPoint : Cemetery X) := by
  change Tendsto (killedMap T r) (𝓝 (Sum.inr ())) (𝓝 (killedMap T r cemeteryPoint))
  rw [nhds_inr, tendsto_map'_iff, killedMap_point]
  exact tendsto_const_nhds

theorem killedMap_continuous_off_singular (T : X → X) (r : X → ℝ)
    (hr : Continuous r) (hT : ∀ x, 0 < r x → ContinuousAt T x)
    (s : Cemetery X) (hs : s ∉ Sum.inl '' {x | ¬ 0 < r x}) :
    ContinuousAt (killedMap T r) s := by
  cases s with
  | inl x =>
    have hx : 0 < r x := by
      by_contra hn
      exact hs ⟨x, hn, rfl⟩
    exact killedMap_continuousAt_regular T r hr x hx (hT x hx)
  | inr u =>
    cases u
    exact killedMap_continuousAt_point T r

theorem killedLog_eq_bot_on_singular (r : X → ℝ)
    (s : Cemetery X) (hs : s ∈ Sum.inl '' {x | ¬ 0 < r x}) :
    extendedLog (killedMultiplier r s) = ⊥ := by
  obtain ⟨x, hx, rfl⟩ := hs
  exact if_neg hx

theorem killedLog_point (r : X → ℝ) :
    extendedLog (killedMultiplier r (cemeteryPoint : Cemetery X)) = ⊥ := by
  simp [extendedLog]

theorem cemetery_compact [CompactSpace X] : IsCompact (univ : Set (Cemetery X)) :=
  isCompact_univ

theorem cemetery_metrizable [TopologicalSpace.MetrizableSpace X] :
    TopologicalSpace.MetrizableSpace (Cemetery X) := by
  letI : MetricSpace X := TopologicalSpace.metrizableSpaceMetric X
  letI : MetricSpace (Cemetery X) := Metric.metricSpaceSum
  infer_instance

end BB
