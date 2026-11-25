import BB.NonlinearTracking

/-!
# Monotone moduli for finite-horizon tracking

Inserting zero in the ratio set makes the supremum well behaved even in the
zero-dimensional space.  All boundedness facts are proved from the actual
strict derivative, before any conditional supremum estimate is used.
-/

noncomputable section
namespace BB.Nonlinear

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def strictRatioSet (G : E → E) (A : E →L[ℝ] E) (r : ℝ) : Set ℝ :=
  insert 0 (remainderRatios G A (Metric.closedBall 0 r))

def strictModulus (G : E → E) (A : E →L[ℝ] E) (r : ℝ) : ℝ := sSup (strictRatioSet G A r)

theorem strictRatioSet_nonempty (G : E → E) (A : E →L[ℝ] E) (r : ℝ) :
    (strictRatioSet G A r).Nonempty := ⟨0, Set.mem_insert _ _⟩

theorem strictRatioSet_upper (G : E → E) (A : E →L[ℝ] E) (r ε : ℝ) (hε : 0 ≤ ε)
    (hrem : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ y ∈ Metric.closedBall (0 : E) r,
      ‖G x - G y - A (x - y)‖ ≤ ε * ‖x - y‖) :
    ∀ q ∈ strictRatioSet G A r, q ≤ ε := by
  intro q hq
  rcases hq with hq | hq
  · simpa only [hq] using hε
  · obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hq
    exact (div_le_iff (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mpr (hrem x hx y hy)

theorem strictRatioSet_bdd (G : E → E) (A : E →L[ℝ] E) (r ε : ℝ) (hε : 0 ≤ ε)
    (hrem : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ y ∈ Metric.closedBall (0 : E) r,
      ‖G x - G y - A (x - y)‖ ≤ ε * ‖x - y‖) :
    BddAbove (strictRatioSet G A r) := ⟨ε, strictRatioSet_upper G A r ε hε hrem⟩

theorem strictModulus_nonneg (G : E → E) (A : E →L[ℝ] E) (r : ℝ)
    (hbdd : BddAbove (strictRatioSet G A r)) : 0 ≤ strictModulus G A r :=
  le_csSup hbdd (Set.mem_insert _ _)

theorem strictModulus_le (G : E → E) (A : E →L[ℝ] E) (r ε : ℝ) (hε : 0 ≤ ε)
    (hrem : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ y ∈ Metric.closedBall (0 : E) r,
      ‖G x - G y - A (x - y)‖ ≤ ε * ‖x - y‖) :
    strictModulus G A r ≤ ε :=
  csSup_le (strictRatioSet_nonempty G A r) (strictRatioSet_upper G A r ε hε hrem)

theorem strictModulus_remainder (G : E → E) (A : E →L[ℝ] E) (r : ℝ)
    (hbdd : BddAbove (strictRatioSet G A r))
    (x y : E) (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) :
    ‖G x - G y - A (x - y)‖ ≤ strictModulus G A r * ‖x - y‖ := by
  by_cases hxy : x = y
  · subst y
    simp
  · have hmem : ‖G x - G y - A (x - y)‖ / ‖x - y‖ ∈ strictRatioSet G A r :=
      Set.mem_insert_of_mem 0 ⟨x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx,
        y, by simpa only [Metric.mem_closedBall, dist_zero_right] using hy, hxy, rfl⟩
    exact (div_le_iff (norm_pos_iff.mpr (sub_ne_zero.mpr hxy))).mp (le_csSup hbdd hmem)

theorem strictModulus_mono (G : E → E) (A : E →L[ℝ] E) (r s : ℝ) (hrs : r ≤ s)
    (hbdd : BddAbove (strictRatioSet G A s)) : strictModulus G A r ≤ strictModulus G A s := by
  apply csSup_le (strictRatioSet_nonempty G A r)
  intro q hq
  apply le_csSup hbdd
  rcases hq with hq | hq
  · subst q
    exact Set.mem_insert _ _
  · obtain ⟨x, hx, y, hy, hxy, hq⟩ := hq
    exact Set.mem_insert_of_mem 0 ⟨x, Metric.closedBall_subset_closedBall hrs hx,
      y, Metric.closedBall_subset_closedBall hrs hy, hxy, hq⟩

/-- The augmented supremum modulus tends to zero at the origin.  For negative
radii the ball is empty; this harmless extension gives an ordinary real limit. -/
theorem strictModulus_tendsto_zero (G : E → E) (A : E →L[ℝ] E)
    (hstrict : HasStrictFDerivAt G A 0) : Tendsto (strictModulus G A) (𝓝 0) (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨b, hb, hrem⟩ := strict_derivative_closed_ball_estimate G A 0 hstrict (ε / 2) (by positivity)
  filter_upwards [eventually_lt_nhds hb] with r hr
  have hremr : ∀ x ∈ Metric.closedBall (0 : E) r, ∀ y ∈ Metric.closedBall (0 : E) r,
      ‖G x - G y - A (x - y)‖ ≤ (ε / 2) * ‖x - y‖ :=
    fun x hx y hy => hrem x (Metric.closedBall_subset_closedBall hr.le hx)
      y (Metric.closedBall_subset_closedBall hr.le hy)
  have hnonneg := strictModulus_nonneg G A r (strictRatioSet_bdd G A r (ε / 2) (by positivity) hremr)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  exact (strictModulus_le G A r (ε / 2) (by positivity) hremr).trans_lt (half_lt_self hε)

variable {A : E →L[ℝ] E} {m M : ℝ}

/-- The complete finite-horizon lemma with a nondecreasing tracking modulus.
The growth constant is chosen before the nonlinear map, making its asserted
uniform dependence on N, τ and the linear-model bounds explicit. -/
theorem PositiveModel.finite_horizon_tracking_modulus (h : PositiveModel A m M)
    (rule : Rule) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ D ≥ 1, ∀ (G : E → E), G 0 = 0 → HasStrictFDerivAt G A 0 →
      ∃ rmax > 0, ∃ ε : ℝ → ℝ,
        MonotoneOn ε (Set.Ioc 0 rmax) ∧
        Tendsto ε (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) ∧
        (∀ r ∈ Set.Ioc 0 rmax, 0 ≤ ε r ∧ ε r ≤ τ / 2) ∧
        ∀ r ∈ Set.Ioc 0 rmax, ∀ p x : E, ‖p‖ ≤ r → ‖x‖ ≤ r → p ≠ x → x ≠ 0 →
          ∀ q ≤ N, (∀ j < q, τ * ‖x‖ ≤ ‖bbCurrent rule A p x j‖) →
            (∀ j ≤ q, ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ ≤ ε r * ‖x‖ ∧
              ‖bbCurrent rule G p x j‖ + ‖bbCurrent rule A p x j‖ ≤ D * ‖x‖) ∧
            (∀ j < q, bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
              G (bbCurrent rule G p x j) ≠ 0 ∧ 0 < bbStep rule G p x j) := by
  obtain ⟨D, S, hD, hDpow, hS, hSbound⟩ := h.tracking_constants N τ hτ
  have hD1 : 0 < D + 1 := by linarith only [hD]
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hSN : 0 < S ^ N := pow_pos hSp N
  let d := m * τ / M
  have hd : 0 < d := div_pos (mul_pos h.m_pos hτ) h.M_pos
  let σ := min 1 (min (τ / 2) (d / 4))
  have hσ : 0 < σ := lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  let ω0 := min (m / 2) (σ / S ^ N)
  have hω0 : 0 < ω0 := lt_min (by exact div_pos h.m_pos (by norm_num)) (div_pos hσ hSN)
  refine ⟨2 * D + 1, by linarith only [hD], ?_⟩
  intro G hG hstrict
  obtain ⟨b, hb, hremb⟩ := strict_derivative_closed_ball_estimate G A 0 hstrict ω0 hω0
  let rmax := b / (D + 1)
  have hrmax : 0 < rmax := div_pos hb hD1
  have hmaxeq : (D + 1) * rmax = b := by dsimp [rmax]; field_simp
  let Ω : ℝ → ℝ := fun r => strictModulus G A ((D + 1) * r)
  let ε : ℝ → ℝ := fun r => Ω r * S ^ N
  have hremr : ∀ r ≤ rmax, ∀ x ∈ Metric.closedBall (0 : E) ((D + 1) * r),
      ∀ y ∈ Metric.closedBall (0 : E) ((D + 1) * r),
        ‖G x - G y - A (x - y)‖ ≤ ω0 * ‖x - y‖ := by
    intro r hr x hx y hy
    have hball : (D + 1) * r ≤ b := by
      rw [← hmaxeq]
      exact mul_le_mul_of_nonneg_left hr hD1.le
    exact hremb x (Metric.closedBall_subset_closedBall hball hx)
      y (Metric.closedBall_subset_closedBall hball hy)
  have hbdd : ∀ r ≤ rmax, BddAbove (strictRatioSet G A ((D + 1) * r)) :=
    fun r hr => strictRatioSet_bdd G A _ ω0 hω0.le (hremr r hr)
  have hΩ : ∀ r ≤ rmax, 0 ≤ Ω r ∧ Ω r ≤ m / 2 ∧ Ω r * S ^ N ≤ σ := by
    intro r hr
    have hnonneg := strictModulus_nonneg G A _ (hbdd r hr)
    have hle := strictModulus_le G A _ ω0 hω0.le (hremr r hr)
    refine ⟨hnonneg, hle.trans (min_le_left _ _), ?_⟩
    exact (le_div_iff hSN).mp (hle.trans (min_le_right _ _))
  refine ⟨rmax, hrmax, ε, ?_, ?_, ?_, ?_⟩
  · intro r _hr s hs hrs
    exact mul_le_mul_of_nonneg_right
      (strictModulus_mono G A _ _ (mul_le_mul_of_nonneg_left hrs hD1.le) (hbdd s hs.2)) hSN.le
  · have harg : Tendsto (fun r : ℝ => (D + 1) * r) (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero] using tendsto_const_nhds.mul (tendsto_id : Tendsto (fun r : ℝ => r) (𝓝 0) (𝓝 0))
    have he : Tendsto ε (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero, zero_mul] using ((strictModulus_tendsto_zero G A hstrict).comp harg).mul_const (S ^ N)
    exact he.mono_left nhdsWithin_le_nhds
  · intro r hr
    exact ⟨mul_nonneg (hΩ r hr.2).1 hSN.le,
      (hΩ r hr.2).2.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩
  · intro r hr p x hp hx hpx hx0 q hq hpre
    have hrem : ∀ u, ‖u‖ ≤ (D + 1) * r → ∀ v, ‖v‖ ≤ (D + 1) * r →
        ‖G u - G v - A (u - v)‖ ≤ Ω r * ‖u - v‖ :=
      fun u hu v hv => strictModulus_remainder G A _ (hbdd r hr.2) u v hu hv
    have ht := h.finite_tracking_explicit rule G p x N q τ r (Ω r) D S d
      hτ hr.1 (hΩ r hr.2).1 (hΩ r hr.2).2.1 hD hDpow hS hd rfl hSbound
      (hΩ r hr.2).2.2 hG hrem hp hx hpx hx0 hq hpre
    refine ⟨?_, ht.2⟩
    intro j hj
    refine ⟨(ht.1 j hj).1.trans ?_, (ht.1 j hj).2⟩
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right hS (hj.trans hq)) (hΩ r hr.2).1) (norm_nonneg x)

end BB.Nonlinear
