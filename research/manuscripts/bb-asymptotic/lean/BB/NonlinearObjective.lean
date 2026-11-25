import BB.NonlinearAsymptotics

/-!
# Gradient and objective conclusions for nonlinear BB

The objective hypotheses refer to the actual Fréchet gradient on a neighborhood.
The local minimizer, uniform value envelopes, and squared objective root factor
are derived from the strict derivative estimate, rather than assumed.
-/

noncomputable section
namespace BB.Nonlinear

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {m M : ℝ}

theorem rootFactor_eventuallyEq (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) :
    rootFactor u = rootFactor v := by
  apply Filter.limsup_congr
  filter_upwards [h] with n hn
  simp only [rootTerm, hn]

/-- A finite prefix with negative objective gaps is immaterial.  The real root
factor comparison uses the nonnegative tail specified by the manuscript. -/
theorem rootFactor_le_of_eventual_nonnegative_comparison
    (u v : ℕ → ℝ) (hu : ∀ᶠ n in atTop, 0 ≤ u n) (hv : ∀ n, 0 ≤ v n)
    (hvb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm v)) (C : ℝ) (hC : 0 < C)
    (h : ∀ᶠ n in atTop, u n ≤ C * v n) : rootFactor u ≤ rootFactor v := by
  have heq : u =ᶠ[atTop] fun n => max 0 (u n) := by
    filter_upwards [hu] with n hn
    exact (max_eq_right hn).symm
  rw [rootFactor_eventuallyEq u _ heq]
  apply rootFactor_le_of_comparison (fun n => max 0 (u n)) v
    (fun n => le_max_left _ _) hv hvb C hC
  filter_upwards [hu, h] with n hn hn'
  simpa only [max_eq_right hn] using hn'

theorem normalized_gradient_objective_root_bounds
    (u : ℕ → E) (hconv : Tendsto u atTop (𝓝 0))
    (F : E → ℝ) (G : E → E) (c R Cg CF : ℝ)
    (hc : 0 ≤ c) (hR : 0 < R) (hCg : 0 < Cg) (hCF : 0 < CF)
    (hroot : rootFactor (fun n => ‖u n‖) ≤ c)
    (hg : ∀ᶠ n in atTop, ‖G (u n)‖ ≤ Cg * ‖u n‖)
    (hF : ∀ᶠ n in atTop, 0 ≤ F (u n) - F 0 ∧ F (u n) - F 0 ≤ CF * ‖u n‖ ^ 2) :
    rootFactor (fun n => ‖G (u n)‖ / R) ≤ c ∧
      rootFactor (fun n => (F (u n) - F 0) / R ^ 2) ≤ c ^ 2 := by
  have hb := norm_rootTerm_bounded_of_tendsto_zero u hconv
  constructor
  · apply (rootFactor_le_of_comparison (fun n => ‖G (u n)‖ / R)
      (fun n => ‖u n‖) (fun n => div_nonneg (norm_nonneg _) hR.le)
      (fun n => norm_nonneg _) hb (Cg / R) (div_pos hCg hR) ?_).trans hroot
    filter_upwards [hg] with n hn
    simpa only [mul_div_right_comm] using div_le_div_of_nonneg_right hn hR.le
  · have hsqb := rootTerm_pow_bounded (fun n => ‖u n‖) (fun n => norm_nonneg _) hb 2
    have hcomp := rootFactor_le_of_eventual_nonnegative_comparison
      (fun n => (F (u n) - F 0) / R ^ 2) (fun n => ‖u n‖ ^ 2)
      (hF.mono (fun n hn => div_nonneg hn.1 (sq_nonneg R))) (fun n => sq_nonneg _) hsqb
      (CF / R ^ 2) (div_pos hCF (sq_pos_of_pos hR))
      (hF.mono (fun n hn => by
        simpa only [mul_div_right_comm] using div_le_div_of_nonneg_right hn.2 (sq_nonneg R)))
    rw [rootFactor_pow (fun n => ‖u n‖) (fun n => norm_nonneg _) hb 2] at hcomp
    have hr0 := rootFactor_nonneg (fun n => ‖u n‖) (fun n => norm_nonneg _) hb
    have hprod := mul_nonneg (sub_nonneg.mpr hroot) (add_nonneg hc hr0)
    nlinarith only [hcomp, hprod]

variable [CompleteSpace E]

/-- Strict differentiability gives actual gradient and objective comparisons on
one common ball, and hence strict minimality of the stationary point. -/
theorem PositiveModel.local_gradient_objective_comparisons
    (h : PositiveModel A m M) (F : E → ℝ) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0) (R : ℝ) (hR : 0 < R)
    (hgrad : ∀ x, ‖x‖ ≤ R → HasGradientAt F (G x) x) :
    ∃ r > 0, r ≤ R ∧ ∀ x : E, ‖x‖ ≤ r →
      (m / 2) * ‖x‖ ≤ ‖G x‖ ∧ ‖G x‖ ≤ (M + m / 2) * ‖x‖ ∧
      (m / 4) * ‖x‖ ^ 2 ≤ F x - F 0 ∧
      F x - F 0 ≤ ((M + m / 2) / 2) * ‖x‖ ^ 2 := by
  obtain ⟨b, hb, hrem⟩ := strict_derivative_closed_ball_estimate G A 0 hstrict
    (m / 2) (div_pos h.m_pos (by norm_num))
  let r := min b R
  have hr : 0 < r := lt_min hb hR
  have hrb : r ≤ b := min_le_left _ _
  have hrR : r ≤ R := min_le_right _ _
  let S := Metric.closedBall (0 : E) r
  have hzero : (0 : E) ∈ S := by simpa only [S, Metric.mem_closedBall, dist_self] using hr.le
  have hremS : ∀ u ∈ S, ∀ v ∈ S, ‖G u - G v - A (u - v)‖ ≤ (m / 2) * ‖u - v‖ := by
    intro u hu v hv
    apply hrem u (Metric.closedBall_subset_closedBall hrb hu)
      v (Metric.closedBall_subset_closedBall hrb hv)
  have hgradS : ∀ x ∈ S, HasGradientAt F (G x) x := by
    intro x hx
    apply hgrad x
    have hx' : ‖x‖ ≤ r := by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx
    exact hx'.trans hrR
  refine ⟨r, hr, hrR, ?_⟩
  intro x hx
  have hxS : x ∈ S := by simpa only [S, Metric.mem_closedBall, dist_zero_right] using hx
  have hgb := local_gradient_bounds G A S 0 x m M (m / 2) hzero hxS hG
    h.coercive h.norm_upper hremS
  have hsegment : ∀ t ∈ Set.Icc (0 : ℝ) 1, (0 : E) + t • x ∈ S := by
    intro t ht
    have hnorm : ‖t • x‖ ≤ r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans (by simpa using hx)
    simpa only [zero_add, S, Metric.mem_closedBall, dist_zero_right] using hnorm
  have hfb := local_objective_bounds F G A S 0 x m M (m / 2) hzero hG
    hsegment hgradS h.coercive h.norm_upper hremS
  simp only [sub_zero] at hgb
  simp only [zero_add] at hfb
  refine ⟨?_, hgb.2, ?_, hfb.2⟩ <;> nlinarith only [hgb.1, hfb.1]

theorem initialRadius_pos (p x : E) (hpx : p ≠ x) : 0 < max ‖p‖ ‖x‖ := by
  by_contra h
  have hmax : max ‖p‖ ‖x‖ ≤ 0 := le_of_not_gt h
  have hp : p = 0 := norm_eq_zero.mp (le_antisymm ((le_max_left _ _).trans hmax) (norm_nonneg p))
  have hx : x = 0 := norm_eq_zero.mp (le_antisymm ((le_max_right _ _).trans hmax) (norm_nonneg x))
  exact hpx (hp.trans hx.symm)

/-- Local error, gradient and objective envelopes and all three sharp root
bounds, with the paper's common initial-pair normalization. -/
theorem PositiveModel.local_objective_convergence
    (h : PositiveModel A m M) (rule : Rule) (F : E → ℝ) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (c γ R : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hγ : c < γ) (hγ1 : γ < 1) (hR : 0 < R)
    (hgrad : ∀ x, ‖x‖ ≤ R → HasGradientAt F (G x) x)
    (hquad : ∀ β : ℝ, c < β → ∃ C ≥ 1, QuadraticEnvelope rule A β C) :
    ∃ r > 0, r ≤ R ∧ ∃ ρ > 0, ρ ≤ r ∧ ∃ K ≥ 1,
      (∀ z : E, ‖z‖ ≤ r → z ≠ 0 → F 0 < F z) ∧
      ∀ p x : E, ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → p ≠ x →
        (∀ n, ‖bbCurrent rule G p x n‖ ≤ r) ∧
        (∀ n, ‖bbCurrent rule G p x n‖ ≤ K * γ ^ n * max ‖p‖ ‖x‖) ∧
        (∀ n, ‖G (bbCurrent rule G p x n)‖ ≤
          ((M + m / 2) * K) * γ ^ n * max ‖p‖ ‖x‖) ∧
        (∀ n, 0 ≤ F (bbCurrent rule G p x n) - F 0 ∧
          F (bbCurrent rule G p x n) - F 0 ≤
            (((M + m / 2) / 2) * K ^ 2) * γ ^ (2 * n) * (max ‖p‖ ‖x‖) ^ 2) ∧
        (∀ n, bbCurrent rule G p x n ≠ 0 →
          bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
          G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) ∧
        Tendsto (bbCurrent rule G p x) atTop (𝓝 0) ∧
        rootFactor (fun n => ‖bbCurrent rule G p x n‖ / max ‖p‖ ‖x‖) ≤ c ∧
        rootFactor (fun n => ‖G (bbCurrent rule G p x n)‖ / max ‖p‖ ‖x‖) ≤ c ∧
        rootFactor (fun n => (F (bbCurrent rule G p x n) - F 0) / (max ‖p‖ ‖x‖) ^ 2) ≤ c ^ 2 := by
  obtain ⟨r, hr, hrR, hcomparison⟩ := h.local_gradient_objective_comparisons F G hG hstrict R hR hgrad
  obtain ⟨ρ, hρ, hρr, K, hK, hlocal⟩ :=
    h.local_sharp_convergence_of_quadratic_envelopes rule G hG hstrict c γ r hc hc1 hγ hγ1 hr hquad
  have hCg : 0 < M + m / 2 := add_pos h.M_pos (div_pos h.m_pos (by norm_num))
  have hCF : 0 < (M + m / 2) / 2 := div_pos hCg (by norm_num)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hγ0 : 0 < γ := hc.trans_lt hγ
  refine ⟨r, hr, hrR, ρ, hρ, hρr, K, hK, ?_, ?_⟩
  · intro z hz hzne
    have hlow := (hcomparison z hz).2.2.1
    have hpos := mul_pos (div_pos h.m_pos (by norm_num : (0 : ℝ) < 4))
      (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    linarith only [hlow, hpos]
  · intro p x hp hx hpx
    obtain ⟨henv, hdomain, hvalid, hconv, _hrootx⟩ := hlocal p x hp hx (Or.inr hpx)
    have hR0 : 0 < max ‖p‖ ‖x‖ := initialRadius_pos p x hpx
    have henvR : ∀ n, ‖bbCurrent rule G p x n‖ ≤ K * γ ^ n * max ‖p‖ ‖x‖ := by
      intro n
      exact (henv n).trans (mul_le_mul_of_nonneg_left (le_max_right _ _)
        (mul_nonneg hK0.le (pow_nonneg hγ0.le n)))
    have hgc : ∀ n, ‖G (bbCurrent rule G p x n)‖ ≤
        (M + m / 2) * ‖bbCurrent rule G p x n‖ := fun n => (hcomparison _ (hdomain n)).2.1
    have hfc : ∀ n, 0 ≤ F (bbCurrent rule G p x n) - F 0 ∧
        F (bbCurrent rule G p x n) - F 0 ≤ ((M + m / 2) / 2) * ‖bbCurrent rule G p x n‖ ^ 2 := by
      intro n
      have hh := (hcomparison _ (hdomain n)).2.2
      exact ⟨(mul_nonneg (div_nonneg h.m_pos.le (by norm_num)) (sq_nonneg _)).trans hh.1, hh.2⟩
    have hregular : ∀ n, bbCurrent rule G p x n ≠ 0 →
        bbPrevious rule G p x n ≠ bbCurrent rule G p x n :=
      fun n hn => Ne.symm (sub_ne_zero.mp (hvalid n hn).1)
    have hroot := h.convergent_error_rootFactor rule G hG hstrict c hc hc1 hquad p x hconv hregular
    have hroots := normalized_gradient_objective_root_bounds (bbCurrent rule G p x) hconv F G
      c (max ‖p‖ ‖x‖) (M + m / 2) ((M + m / 2) / 2)
      hc hR0 hCg hCF hroot (Filter.eventually_of_forall hgc) (Filter.eventually_of_forall hfc)
    refine ⟨hdomain, henvR, ?_, ?_, hvalid, hconv,
      h.convergent_normalized_error_rootFactor rule G hG hstrict c hc hc1 hquad p x hconv hregular _ hR0,
      hroots.1, hroots.2⟩
    · intro n
      calc
        _ ≤ (M + m / 2) * ‖bbCurrent rule G p x n‖ := hgc n
        _ ≤ (M + m / 2) * (K * γ ^ n * max ‖p‖ ‖x‖) :=
          mul_le_mul_of_nonneg_left (henvR n) hCg.le
        _ = _ := by ring
    · intro n
      refine ⟨(hfc n).1, ?_⟩
      have hn := henvR n
      have hsquare : ‖bbCurrent rule G p x n‖ ^ 2 ≤ (K * γ ^ n * max ‖p‖ ‖x‖) ^ 2 := by
        have hnn := norm_nonneg (bbCurrent rule G p x n)
        nlinarith only [hn, hnn]
      calc
        _ ≤ ((M + m / 2) / 2) * ‖bbCurrent rule G p x n‖ ^ 2 := (hfc n).2
        _ ≤ ((M + m / 2) / 2) * (K * γ ^ n * max ‖p‖ ‖x‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hsquare hCF.le
        _ = _ := by simp only [mul_pow, ← pow_mul, Nat.mul_comm]; ring

/-- All three bounds for any convergent regular trajectory, including one
started outside the local convergence neighborhood.  Nonnegativity of the
objective gap is proved on a tail. -/
theorem PositiveModel.convergent_objective_rootFactors
    (h : PositiveModel A m M) (rule : Rule) (F : E → ℝ) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (c R : ℝ) (hc : 0 ≤ c) (hc1 : c < 1) (hR : 0 < R)
    (hgrad : ∀ z, ‖z‖ ≤ R → HasGradientAt F (G z) z)
    (hquad : ∀ β : ℝ, c < β → ∃ C ≥ 1, QuadraticEnvelope rule A β C)
    (p x : E) (hconv : Tendsto (bbCurrent rule G p x) atTop (𝓝 0))
    (hregular : ∀ n, bbCurrent rule G p x n ≠ 0 →
      bbPrevious rule G p x n ≠ bbCurrent rule G p x n)
    (R0 : ℝ) (hR0 : 0 < R0) :
    (∀ᶠ n in atTop, 0 ≤ F (bbCurrent rule G p x n) - F 0) ∧
      rootFactor (fun n => ‖bbCurrent rule G p x n‖ / R0) ≤ c ∧
      rootFactor (fun n => ‖G (bbCurrent rule G p x n)‖ / R0) ≤ c ∧
      rootFactor (fun n => (F (bbCurrent rule G p x n) - F 0) / R0 ^ 2) ≤ c ^ 2 := by
  obtain ⟨r, hr, _hrR, hcomparison⟩ := h.local_gradient_objective_comparisons F G hG hstrict R hR hgrad
  have hnormlim := tendsto_zero_iff_norm_tendsto_zero.mp hconv
  have hsmall : ∀ᶠ n in atTop, ‖bbCurrent rule G p x n‖ ≤ r :=
    ((tendsto_order.mp hnormlim).2 r hr).mono (fun _ hn => hn.le)
  have hg : ∀ᶠ n in atTop, ‖G (bbCurrent rule G p x n)‖ ≤
      (M + m / 2) * ‖bbCurrent rule G p x n‖ := hsmall.mono (fun n hn => (hcomparison _ hn).2.1)
  have hF : ∀ᶠ n in atTop, 0 ≤ F (bbCurrent rule G p x n) - F 0 ∧
      F (bbCurrent rule G p x n) - F 0 ≤ ((M + m / 2) / 2) * ‖bbCurrent rule G p x n‖ ^ 2 := by
    filter_upwards [hsmall] with n hn
    have hh := (hcomparison _ hn).2.2
    exact ⟨(mul_nonneg (div_nonneg h.m_pos.le (by norm_num)) (sq_nonneg _)).trans hh.1, hh.2⟩
  have hCg : 0 < M + m / 2 := add_pos h.M_pos (div_pos h.m_pos (by norm_num))
  have hroot := h.convergent_error_rootFactor rule G hG hstrict c hc hc1 hquad p x hconv hregular
  have hroots := normalized_gradient_objective_root_bounds (bbCurrent rule G p x) hconv F G
    c R0 (M + m / 2) ((M + m / 2) / 2) hc hR0 hCg (div_pos hCg (by norm_num)) hroot hg hF
  exact ⟨hF.mono (fun _ hn => hn.1),
    h.convergent_normalized_error_rootFactor rule G hG hstrict c hc hc1 hquad p x hconv hregular R0 hR0,
    hroots.1, hroots.2⟩

end BB.Nonlinear
