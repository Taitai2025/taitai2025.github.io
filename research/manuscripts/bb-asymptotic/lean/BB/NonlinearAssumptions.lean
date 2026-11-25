import BB.NonlinearModulus

/-!
# The source's two-point modulus and strict differentiation

The real supremum is used only after boundedness has been established.
This file proves both directions of the small-radius modulus criterion, so
the source's explicit linearization assumption and mathlib's strict Fréchet
derivative have a checked interface.
-/

noncomputable section
namespace BB.Nonlinear
open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem remainderRatios_closedBall_nonempty [Nontrivial E]
    (G : E → E) (A : E →L[ℝ] E) (a : E) (r : ℝ) (hr : 0 < r) :
    (remainderRatios G A (Metric.closedBall a r)).Nonempty := by
  obtain ⟨v,hv⟩ := exists_norm_eq E hr.le
  have hne : a+v ≠ a := by
    intro he
    have hz : v = 0 := add_left_cancel (show a+v = a+0 by simpa only [add_zero] using he)
    rw [hz,norm_zero] at hv
    linarith
  refine ⟨_, a+v, ?_, a, ?_, hne, rfl⟩
  · simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv] using (le_refl r)
  · simpa only [Metric.mem_closedBall, dist_self] using hr.le

/-- On the source's nonempty, bounded quotient set, adjoining zero does not
change its literal real supremum. -/
theorem strictModulus_eq_remainderModulus (G : E → E) (A : E →L[ℝ] E) (r : ℝ)
    (hne : (remainderRatios G A (Metric.closedBall 0 r)).Nonempty)
    (hbdd : BddAbove (remainderRatios G A (Metric.closedBall 0 r))) :
    strictModulus G A r = remainderModulus G A (Metric.closedBall 0 r) := by
  have hb : BddAbove (strictRatioSet G A r) := by
    obtain ⟨C,hC⟩ := hbdd
    refine ⟨max 0 C, ?_⟩
    rintro q (rfl | hq)
    · exact le_max_left _ _
    · exact (hC hq).trans (le_max_right _ _)
  apply le_antisymm
  · apply csSup_le (strictRatioSet_nonempty G A r)
    rintro q (rfl | hq)
    · exact remainder_modulus_nonneg G A _ hne hbdd
    · exact le_csSup hbdd hq
  · apply csSup_le hne
    intro q hq
    exact le_csSup hb (Set.mem_insert_of_mem 0 hq)

theorem strict_derivative_of_closed_ball_estimates (G : E → E) (A : E →L[ℝ] E)
    (a : E)
    (hest : ∀ ε > 0, ∃ r > 0, ∀ x ∈ Metric.closedBall a r,
      ∀ y ∈ Metric.closedBall a r, ‖G x - G y - A (x-y)‖ ≤ ε * ‖x-y‖) :
    HasStrictFDerivAt G A a := by
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  obtain ⟨r, hr, hrem⟩ := hest ε hε
  filter_upwards [Metric.ball_mem_nhds (a,a) hr] with p hp
  rw [← ball_prod_same, mem_prod] at hp
  exact hrem p.1 (Metric.ball_subset_closedBall hp.1)
    p.2 (Metric.ball_subset_closedBall hp.2)

theorem strict_derivative_iff_closed_ball_estimates (G : E → E) (A : E →L[ℝ] E)
    (a : E) : HasStrictFDerivAt G A a ↔
      ∀ ε > 0, ∃ r > 0, ∀ x ∈ Metric.closedBall a r,
        ∀ y ∈ Metric.closedBall a r, ‖G x-G y-A (x-y)‖ ≤ ε*‖x-y‖ :=
  ⟨fun h ε hε => strict_derivative_closed_ball_estimate G A a h ε hε,
    strict_derivative_of_closed_ball_estimates G A a⟩

theorem strict_derivative_of_modulus (G : E → E) (A : E →L[ℝ] E)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hbdd : ∀ r ∈ Ioc 0 r₀, BddAbove (strictRatioSet G A r))
    (hlim : Tendsto (strictModulus G A) (nhdsWithin 0 (Ioi 0)) (𝓝 0)) :
    HasStrictFDerivAt G A 0 := by
  apply strict_derivative_of_closed_ball_estimates
  intro ε hε
  have he : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), strictModulus G A r < ε :=
    hlim (eventually_lt_nhds hε)
  have hp : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), 0 < r := self_mem_nhdsWithin
  have hb : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), r < r₀ :=
    (eventually_lt_nhds hr₀).filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hpr, hbr, her⟩ := (hp.and (hb.and he)).exists
  refine ⟨r, hpr, ?_⟩
  intro x hx y hy
  have h := strictModulus_remainder G A r (hbdd r ⟨hpr,hbr.le⟩) x y
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
    (by simpa only [Metric.mem_closedBall, dist_zero_right] using hy)
  exact h.trans (mul_le_mul_of_nonneg_right her.le (norm_nonneg _))

theorem strict_derivative_iff_modulus (G : E → E) (A : E →L[ℝ] E) :
    HasStrictFDerivAt G A 0 ↔
      (∃ r₀ > 0, ∀ r ∈ Ioc 0 r₀, BddAbove (strictRatioSet G A r)) ∧
      Tendsto (strictModulus G A) (nhdsWithin 0 (Ioi 0)) (𝓝 0) := by
  constructor
  · intro h
    obtain ⟨r₀, hr₀, hrem⟩ := strict_derivative_closed_ball_estimate G A 0 h 1 zero_lt_one
    refine ⟨⟨r₀, hr₀, ?_⟩, (strictModulus_tendsto_zero G A h).mono_left nhdsWithin_le_nhds⟩
    intro r hr
    apply strictRatioSet_bdd G A r 1 zero_le_one
    intro x hx y hy
    exact hrem x (Metric.closedBall_subset_closedBall hr.2 hx)
      y (Metric.closedBall_subset_closedBall hr.2 hy)
  · rintro ⟨⟨r₀, hr₀, hbdd⟩, hlim⟩
    exact strict_derivative_of_modulus G A r₀ hr₀ hbdd hlim

end BB.Nonlinear
