import BB.NonlinearConvergence

/-!
# Root factors of every convergent nonlinear BB trajectory

These statements do not require the original pair to belong to one of the
local neighborhoods.  A convergent, nonterminally regular trajectory eventually
enters each required neighborhood, and the unchanged actual tail is restarted.
-/

noncomputable section
namespace BB.Nonlinear

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {m M : ℝ}

theorem norm_rootTerm_bounded_of_tendsto_zero (u : ℕ → E)
    (hu : Tendsto u atTop (𝓝 0)) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => ‖u n‖)) := by
  have hn : Tendsto (fun n => ‖u n‖) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mp hu
  have hsmall : ∀ᶠ n in atTop, ‖u n‖ < 1 := (tendsto_order.mp hn).2 1 zero_lt_one
  apply rootTerm_bounded_of_eventual_envelope (fun n => ‖u n‖)
    (fun n => norm_nonneg _) 1 1 zero_lt_one zero_le_one
  filter_upwards [hsmall] with n hn
  simpa only [one_pow, one_mul] using hn.le

/-- Every convergent trajectory whose nonterminal incoming secants are
nonzero has the sharp error root bound, regardless of its initial location. -/
theorem PositiveModel.convergent_error_rootFactor
    (h : PositiveModel A m M) (rule : Rule) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hquad : ∀ β : ℝ, c < β → ∃ C ≥ 1, QuadraticEnvelope rule A β C)
    (p x : E) (hconv : Tendsto (bbCurrent rule G p x) atTop (𝓝 0))
    (hregular : ∀ n, bbCurrent rule G p x n ≠ 0 →
      bbPrevious rule G p x n ≠ bbCurrent rule G p x n) :
    rootFactor (fun n => ‖bbCurrent rule G p x n‖) ≤ c := by
  have hnormlim := tendsto_zero_iff_norm_tendsto_zero.mp hconv
  apply le_of_forall_strict_upper_bound
  intro ε hcε
  obtain ⟨δ, hcδ, hδ⟩ := exists_between (lt_min hcε hc1)
  have hδ1 : δ < 1 := hδ.trans_le (min_le_right ε 1)
  have hδε : δ < ε := hδ.trans_le (min_le_left ε 1)
  have hδ0 : 0 < δ := hc.trans_lt hcδ
  obtain ⟨β, hcβ, hβδ⟩ := exists_between hcδ
  obtain ⟨C, hC, henv⟩ := hquad β hcβ
  obtain ⟨ρ, hρ, _hρR, K, hK, hlocal⟩ :=
    h.local_convergence_of_quadratic_envelope rule G hG hstrict β δ C 1
      (hc.trans_lt hcβ) hβδ hδ1 hC zero_lt_one henv
  have hsmall : ∀ᶠ n in atTop, ‖bbCurrent rule G p x n‖ < ρ :=
    (tendsto_order.mp hnormlim).2 ρ hρ
  obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp hsmall
  have hpρ : ‖bbPrevious rule G p x (k + 1)‖ ≤ ρ := by
    rw [bbPrevious_succ]
    exact (hk k le_rfl).le
  have hxρ : ‖bbCurrent rule G p x (k + 1)‖ ≤ ρ := (hk (k + 1) (by omega)).le
  have hregρ : bbCurrent rule G p x (k + 1) = 0 ∨
      bbPrevious rule G p x (k + 1) ≠ bbCurrent rule G p x (k + 1) := by
    by_cases hz : bbCurrent rule G p x (k + 1) = 0
    · exact Or.inl hz
    · exact Or.inr (hregular (k + 1) hz)
  have htail := (hlocal (bbPrevious rule G p x (k + 1))
    (bbCurrent rule G p x (k + 1)) hpρ hxρ hregρ).1
  let Cδ := K * (‖bbCurrent rule G p x (k + 1)‖ + 1)
  have hCδ : 0 < Cδ := mul_pos (lt_of_lt_of_le zero_lt_one hK) (by positivity)
  have htailbound : ∀ n, ‖bbCurrent rule G p x (n + (k + 1))‖ ≤ Cδ * δ ^ n := by
    intro n
    rw [Nat.add_comm n, bbCurrent_add]
    apply (htail n).trans
    dsimp [Cδ]
    have hz := mul_nonneg (le_trans zero_le_one hK) (pow_nonneg hδ0.le n)
    nlinarith only [hz]
  have htailroot := rootFactor_le_of_envelope (fun n => ‖bbCurrent rule G p x (n + (k + 1))‖)
    (fun n => norm_nonneg _) δ hδ0.le ⟨Cδ, hCδ, htailbound⟩
  have htailbounded := rootTerm_bounded_of_eventual_envelope
    (fun n => ‖bbCurrent rule G p x (n + (k + 1))‖) (fun n => norm_nonneg _)
    Cδ δ hCδ hδ0.le (Filter.eventually_of_forall htailbound)
  exact ((rootFactor_le_shift (fun n => ‖bbCurrent rule G p x n‖)
    (fun n => norm_nonneg _) (k + 1) htailbounded).trans htailroot).trans hδε.le

/-- Fixed positive normalization leaves the convergent error root bound unchanged. -/
theorem PositiveModel.convergent_normalized_error_rootFactor
    (h : PositiveModel A m M) (rule : Rule) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hquad : ∀ β : ℝ, c < β → ∃ C ≥ 1, QuadraticEnvelope rule A β C)
    (p x : E) (hconv : Tendsto (bbCurrent rule G p x) atTop (𝓝 0))
    (hregular : ∀ n, bbCurrent rule G p x n ≠ 0 →
      bbPrevious rule G p x n ≠ bbCurrent rule G p x n)
    (R : ℝ) (hR : 0 < R) :
    rootFactor (fun n => ‖bbCurrent rule G p x n‖ / R) ≤ c := by
  rw [rootFactor_div_const (fun n => ‖bbCurrent rule G p x n‖)
    (fun n => norm_nonneg _) (norm_rootTerm_bounded_of_tendsto_zero _ hconv) R hR]
  exact h.convergent_error_rootFactor rule G hG hstrict c hc hc1 hquad p x hconv hregular

end BB.Nonlinear
