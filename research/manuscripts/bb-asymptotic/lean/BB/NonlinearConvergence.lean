import BB.NonlinearTracking
import BB.Asymptotics

/-!
# Local convergence of the actual nonlinear BB trajectory

The only quadratic convergence input is `QuadraticEnvelope`: an envelope for the
actual frozen BB orbit, uniform in its initial current point and incoming secant.
All nonlinear comparison, stopping, and restart arguments are proved here.
-/

noncomputable section

namespace BB.Nonlinear

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A quadratic envelope uniform in the current point and arbitrary incoming secant. -/
def QuadraticEnvelope (rule : Rule) (A : E →L[ℝ] E) (β C : ℝ) : Prop :=
  ∀ p x : E, p ≠ x → ∀ n, ‖bbCurrent rule A p x n‖ ≤ C * β ^ n * ‖x‖

/-- Reindexing an actual BB state preserves the algorithm, including its secant. -/
theorem bbState_add (rule : Rule) (G : E → E) (p x : E) (k n : ℕ) :
    bbState rule G p x (k + n) =
      bbState rule G (bbPrevious rule G p x k) (bbCurrent rule G p x k) n := by
  induction n with
  | zero => simp [bbState, bbPrevious, bbCurrent]
  | succ n ih => simpa only [Nat.add_succ, bbState] using congrArg (bbTransition rule G) ih

theorem bbCurrent_add (rule : Rule) (G : E → E) (p x : E) (k n : ℕ) :
    bbCurrent rule G p x (k + n) =
      bbCurrent rule G (bbPrevious rule G p x k) (bbCurrent rule G p x k) n := by
  exact congrArg Prod.snd (bbState_add rule G p x k n)

theorem bbPrevious_add (rule : Rule) (G : E → E) (p x : E) (k n : ℕ) :
    bbPrevious rule G p x (k + n) =
      bbPrevious rule G (bbPrevious rule G p x k) (bbCurrent rule G p x k) n := by
  exact congrArg Prod.fst (bbState_add rule G p x k n)

theorem bbStep_add (rule : Rule) (G : E → E) (p x : E) (k n : ℕ) :
    bbStep rule G p x (k + n) =
      bbStep rule G (bbPrevious rule G p x k) (bbCurrent rule G p x k) n := by
  simp only [bbStep, bbCurrent_add, bbPrevious_add]

/-- Once the current point is zero, the actual recurrence remains there. -/
theorem bbCurrent_zero_initial (rule : Rule) (G : E → E) (hG : G 0 = 0) (p : E) :
    ∀ n, bbCurrent rule G p 0 n = 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact bb_zero_next rule G p 0 hG n ih

/-- A gap between quadratic and desired rates gives a finite comparison horizon. -/
theorem exists_comparison_horizon (β γ C : ℝ)
    (hβ : 0 < β) (hβγ : β < γ) (hC : 1 ≤ C) :
    ∃ N ≥ 1, C * β ^ N ≤ γ ^ N / 4 := by
  have hγ : 0 < γ := hβ.trans hβγ
  have hCp : 0 < C := by linarith
  have hratio : 0 ≤ β / γ := by positivity
  have hratio1 : β / γ < 1 := (div_lt_one hγ).mpr hβγ
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < 1 / (4 * C)) hratio1
  refine ⟨n + 1, by omega, ?_⟩
  have hsmall : (β / γ) ^ (n + 1) ≤ 1 / (4 * C) :=
    (pow_le_pow_of_le_one hratio hratio1.le (by omega : n ≤ n + 1)).trans hn.le
  have hcsmall : C * (β / γ) ^ (n + 1) ≤ 1 / 4 := by
    calc
      _ ≤ C * (1 / (4 * C)) := mul_le_mul_of_nonneg_left hsmall hCp.le
      _ = 1 / 4 := by field_simp; ring
  rw [div_pow, ← mul_div_assoc] at hcsmall
  have hmul := (div_le_iff (pow_pos hγ (n + 1))).mp hcsmall
  nlinarith only [hmul]

variable {A : E →L[ℝ] E} {m M : ℝ}

/-- A genuine contracting block of the actual nonlinear BB orbit.

The endpoint index is the first quadratic threshold crossing.  The proof also
establishes the incoming-secant condition needed to restart at that endpoint.
-/
theorem PositiveModel.nonlinear_contracting_block (h : PositiveModel A m M) (rule : Rule)
    (G : E → E) (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (β γ C : ℝ) (hβ : 0 < β) (hβγ : β < γ) (hγ1 : γ < 1) (hC : 1 ≤ C)
    (hquad : QuadraticEnvelope rule A β C) :
    ∃ N ≥ 1, ∃ D ≥ 1, ∃ r > 0, ∀ p x : E, ‖p‖ ≤ r → ‖x‖ ≤ r → (x = 0 ∨ p ≠ x) →
      ∃ q, 1 ≤ q ∧ q ≤ N ∧
        ‖bbCurrent rule G p x q‖ ≤ γ ^ q * ‖x‖ ∧
        (∀ j ≤ q, ‖bbCurrent rule G p x j‖ ≤ D * ‖x‖) ∧
        (bbCurrent rule G p x q = 0 ∨ bbPrevious rule G p x q ≠ bbCurrent rule G p x q) ∧
        (∀ j < q, bbCurrent rule G p x j ≠ 0 →
          bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
          G (bbCurrent rule G p x j) ≠ 0 ∧ 0 < bbStep rule G p x j) := by
  have hγ : 0 < γ := hβ.trans hβγ
  obtain ⟨N, hN, hNrate⟩ := exists_comparison_horizon β γ C hβ hβγ hC
  let τ := γ ^ N / 4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hγNle : γ ^ N ≤ 1 := by
    simpa using pow_le_pow_of_le_one hγ.le hγ1.le (Nat.zero_le N)
  have hτ1 : τ < 1 := by dsimp [τ]; linarith
  obtain ⟨D, hD, r, hr, htrack⟩ := h.finite_horizon_tracking rule G hG hstrict N τ (τ / 2) hτ (by positivity)
  refine ⟨N, hN, D, hD, r, hr, ?_⟩
  intro p x hp hx hregular
  by_cases hx0 : x = 0
  · subst x
    refine ⟨1, le_rfl, hN, ?_, ?_, Or.inl ?_, ?_⟩
    · simp [bbCurrent_zero_initial rule G hG]
    · intro j _
      simp [bbCurrent_zero_initial rule G hG]
    · exact bbCurrent_zero_initial rule G hG p 1
    · intro j _ hj
      exact False.elim (hj (bbCurrent_zero_initial rule G hG p j))
  · have hpx : p ≠ x := hregular.resolve_left hx0
    have hR : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hatN : ‖bbCurrent rule A p x N‖ ≤ τ * ‖x‖ :=
      (hquad p x hpx N).trans (mul_le_mul_of_nonneg_right hNrate hR.le)
    have hex : ∃ q, ‖bbCurrent rule A p x q‖ ≤ τ * ‖x‖ := ⟨N, hatN⟩
    let q := Nat.find hex
    have hhit : ‖bbCurrent rule A p x q‖ ≤ τ * ‖x‖ := Nat.find_spec hex
    have hqN : q ≤ N := Nat.find_min' hex hatN
    have hqpos : 0 < q := by
      by_contra hq
      have hqz : q = 0 := by omega
      rw [hqz, bbCurrent_zero] at hhit
      have hpos := mul_pos (sub_pos.mpr hτ1) hR
      nlinarith only [hhit, hpos]
    have hpre : ∀ j < q, τ * ‖x‖ ≤ ‖bbCurrent rule A p x j‖ := by
      intro j hj
      exact (lt_of_not_ge (Nat.find_min hex hj)).le
    have ht := htrack p x hp hx hpx hx0 q hqN hpre
    have hcontract : ‖bbCurrent rule G p x q‖ ≤ γ ^ q * ‖x‖ := by
      have he := (ht.1 q le_rfl).1
      have hn : ‖bbCurrent rule G p x q‖ - ‖bbCurrent rule A p x q‖ ≤
          ‖bbCurrent rule G p x q - bbCurrent rule A p x q‖ := norm_sub_norm_le _ _
      have hpow : γ ^ N ≤ γ ^ q := pow_le_pow_of_le_one hγ.le hγ1.le hqN
      have hpowR := mul_le_mul_of_nonneg_right hpow hR.le
      dsimp [τ] at he hhit
      have hnonneg := mul_nonneg (pow_nonneg hγ.le N) hR.le
      nlinarith only [he, hn, hhit, hpowR, hnonneg]
    have hlast : bbCurrent rule G p x q - bbPrevious rule G p x q ≠ 0 := by
      have heq : q = (q - 1) + 1 := by omega
      have hv := ht.2 (q - 1) (by omega)
      rw [heq, bb_secant_succ]
      exact smul_ne_zero (neg_ne_zero.mpr hv.2.2.ne') hv.2.1
    refine ⟨q, hqpos, hqN, hcontract, ?_, Or.inr (Ne.symm (sub_ne_zero.mp hlast)), ?_⟩
    · intro j hj
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (ht.1 j hj).2
    · intro j hj _
      exact ht.2 j hj

/-- Restarting the actual orbit at its constructed block endpoints gives a
uniform estimate at every time.  This induction also propagates the domain and
the nonterminal secant conditions; no infinite sequence of admissible blocks is
assumed. -/
theorem restart_envelope_of_contracting_blocks
    (rule : Rule) (G : E → E) (γ : ℝ) (N : ℕ) (D r : ℝ)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hD : 1 ≤ D) (_hr : 0 < r)
    (hblock : ∀ p x : E, ‖p‖ ≤ r → ‖x‖ ≤ r → (x = 0 ∨ p ≠ x) →
      ∃ q, 1 ≤ q ∧ q ≤ N ∧
        ‖bbCurrent rule G p x q‖ ≤ γ ^ q * ‖x‖ ∧
        (∀ j ≤ q, ‖bbCurrent rule G p x j‖ ≤ D * ‖x‖) ∧
        (bbCurrent rule G p x q = 0 ∨ bbPrevious rule G p x q ≠ bbCurrent rule G p x q) ∧
        (∀ j < q, bbCurrent rule G p x j ≠ 0 →
          bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
          G (bbCurrent rule G p x j) ≠ 0 ∧ 0 < bbStep rule G p x j)) :
    ∀ n (p x : E), ‖p‖ ≤ r → ‖x‖ ≤ r / D → (x = 0 ∨ p ≠ x) →
      ‖bbCurrent rule G p x n‖ ≤ (D / γ ^ N) * γ ^ n * ‖x‖ ∧
      ‖bbCurrent rule G p x n‖ ≤ D * ‖x‖ ∧
      (bbCurrent rule G p x n ≠ 0 →
        bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
        G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) := by
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hCN : 0 < D / γ ^ N := div_pos hDp (pow_pos hγ N)
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p x hp hx hregular
    have hDx : D * ‖x‖ ≤ r := by
      have hx' := (le_div_iff hDp).mp hx
      simpa only [mul_comm] using hx'
    have hxD : ‖x‖ ≤ D * ‖x‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hD (norm_nonneg x)
    obtain ⟨q, hq, hqN, hcontract, hgrowth, hend, hvalid⟩ :=
      hblock p x hp (hxD.trans hDx) hregular
    by_cases hnq : n < q
    · have hnN : n ≤ N := by omega
      have hpow : γ ^ N ≤ γ ^ n := pow_le_pow_of_le_one hγ.le hγ1.le hnN
      have hfactor : D ≤ D / γ ^ N * γ ^ n := by
        calc
          D = D / γ ^ N * γ ^ N := by field_simp
          _ ≤ D / γ ^ N * γ ^ n := mul_le_mul_of_nonneg_left hpow hCN.le
      exact ⟨(hgrowth n hnq.le).trans
        (mul_le_mul_of_nonneg_right hfactor (norm_nonneg x)),
        hgrowth n hnq.le, hvalid n hnq⟩
    · have hqn : q ≤ n := le_of_not_gt hnq
      have hsub : n - q < n := by omega
      have hqeq : q = (q - 1) + 1 := by omega
      have hpnext : ‖bbPrevious rule G p x q‖ ≤ r := by
        rw [hqeq, bbPrevious_succ]
        exact (hgrowth (q - 1) (by omega)).trans hDx
      have hpowone : γ ^ q ≤ 1 := by
        simpa using pow_le_pow_of_le_one hγ.le hγ1.le (Nat.zero_le q)
      have hnext : ‖bbCurrent rule G p x q‖ ≤ ‖x‖ :=
        hcontract.trans (by simpa only [one_mul] using
          mul_le_mul_of_nonneg_right hpowone (norm_nonneg x))
      have he := ih (n - q) hsub (bbPrevious rule G p x q)
        (bbCurrent rule G p x q) hpnext (hnext.trans hx) hend
      have hadd : q + (n - q) = n := Nat.add_sub_of_le hqn
      have hcur := bbCurrent_add rule G p x q (n - q)
      have hprev := bbPrevious_add rule G p x q (n - q)
      have hstep := bbStep_add rule G p x q (n - q)
      rw [hadd] at hcur hprev hstep
      refine ⟨?_, ?_, ?_⟩
      · rw [hcur]
        calc
          _ ≤ (D / γ ^ N) * γ ^ (n - q) * ‖bbCurrent rule G p x q‖ := he.1
          _ ≤ (D / γ ^ N) * γ ^ (n - q) * (γ ^ q * ‖x‖) :=
            mul_le_mul_of_nonneg_left hcontract
              (mul_nonneg hCN.le (pow_nonneg hγ.le _))
          _ = (D / γ ^ N) * γ ^ n * ‖x‖ := by
            calc
              _ = (D / γ ^ N) * (γ ^ (n - q) * γ ^ q) * ‖x‖ := by ring
              _ = _ := by rw [← pow_add, Nat.sub_add_cancel hqn]
      · rw [hcur]
        exact he.2.1.trans (mul_le_mul_of_nonneg_left hnext hDp.le)
      · rw [hcur, hprev, hstep]
        exact he.2.2

/-- Local R-linear convergence for the actual nonlinear BB recurrence.  The
sole rate input is a uniform envelope for the frozen quadratic BB recurrence;
all finite-horizon comparison and actual-orbit restarts are discharged above.
The radius can be required to lie below any prescribed positive radius. -/
theorem PositiveModel.local_convergence_of_quadratic_envelope
    (h : PositiveModel A m M) (rule : Rule) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (β γ C R : ℝ) (hβ : 0 < β) (hβγ : β < γ) (hγ1 : γ < 1)
    (hC : 1 ≤ C) (hR : 0 < R) (hquad : QuadraticEnvelope rule A β C) :
    ∃ ρ > 0, ρ ≤ R ∧ ∃ K ≥ 1, ∀ p x : E,
      ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → (x = 0 ∨ p ≠ x) →
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ K * γ ^ n * ‖x‖) ∧
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ R) ∧
      (∀ n, bbCurrent rule G p x n ≠ 0 →
        bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
        G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) := by
  have hγ : 0 < γ := hβ.trans hβγ
  obtain ⟨N, _hN, D, hD, r, hr, hblock⟩ :=
    h.nonlinear_contracting_block rule G hG hstrict β γ C hβ hβγ hγ1 hC hquad
  have hDp : 0 < D := lt_of_lt_of_le zero_lt_one hD
  let ρ := min r R / D
  have hρ : 0 < ρ := div_pos (lt_min hr hR) hDp
  have hρr : ρ ≤ r / D := div_le_div_of_nonneg_right (min_le_left r R) hDp.le
  have hρR : ρ ≤ R / D := div_le_div_of_nonneg_right (min_le_right r R) hDp.le
  have hDρ : D * ρ ≤ R := by
    have hx := (le_div_iff hDp).mp hρR
    simpa only [mul_comm] using hx
  have hρleR : ρ ≤ R := by nlinarith only [hDρ, hD, hρ]
  have hpow : γ ^ N ≤ 1 := by
    simpa using pow_le_pow_of_le_one hγ.le hγ1.le (Nat.zero_le N)
  have hK : 1 ≤ D / γ ^ N := (le_div_iff (pow_pos hγ N)).mpr (by nlinarith only [hpow, hD])
  refine ⟨ρ, hρ, hρleR, D / γ ^ N, hK, ?_⟩
  intro p x hp hx hregular
  have hpr : ‖p‖ ≤ r := by
    have hpp := (le_div_iff hDp).mp (hp.trans hρr)
    have hpD := mul_le_mul_of_nonneg_right hD (norm_nonneg p)
    nlinarith only [hpp, hpD]
  have he := fun n => restart_envelope_of_contracting_blocks rule G γ N D r
    hγ hγ1 hD hr hblock n p x hpr (hx.trans hρr) hregular
  refine ⟨fun n => (he n).1, ?_, fun n => (he n).2.2⟩
  intro n
  exact (he n).2.1.trans ((mul_le_mul_of_nonneg_left hx hDp.le).trans hDρ)

/-- The full local sharp-root conclusion.  One prescribed rate controls a
uniform neighborhood.  For each sharper rate, convergence enters the smaller
neighborhood for that rate, and the actual recurrence is restarted there. -/
theorem PositiveModel.local_sharp_convergence_of_quadratic_envelopes
    (h : PositiveModel A m M) (rule : Rule) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (c γ R : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hγ : c < γ) (hγ1 : γ < 1) (hR : 0 < R)
    (hquad : ∀ β : ℝ, c < β → ∃ C ≥ 1, QuadraticEnvelope rule A β C) :
    ∃ ρ > 0, ρ ≤ R ∧ ∃ K ≥ 1, ∀ p x : E,
      ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → (x = 0 ∨ p ≠ x) →
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ K * γ ^ n * ‖x‖) ∧
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ R) ∧
      (∀ n, bbCurrent rule G p x n ≠ 0 →
        bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
        G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) ∧
      Tendsto (bbCurrent rule G p x) atTop (𝓝 0) ∧
      rootFactor (fun n => ‖bbCurrent rule G p x n‖ / ‖x‖) ≤ c := by
  have hγ0 : 0 < γ := hc.trans_lt hγ
  have hlocal : ∀ δ : ℝ, c < δ → δ < 1 →
      ∃ ρ > 0, ρ ≤ R ∧ ∃ K ≥ 1, ∀ p x : E,
        ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → (x = 0 ∨ p ≠ x) →
        (∀ n, ‖bbCurrent rule G p x n‖ ≤ K * δ ^ n * ‖x‖) ∧
        (∀ n, ‖bbCurrent rule G p x n‖ ≤ R) ∧
        (∀ n, bbCurrent rule G p x n ≠ 0 →
          bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
          G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) := by
    intro δ hcδ hδ1
    obtain ⟨β, hcβ, hβδ⟩ := exists_between hcδ
    obtain ⟨C, hC, henv⟩ := hquad β hcβ
    exact h.local_convergence_of_quadratic_envelope rule G hG hstrict β δ C R
      (hc.trans_lt hcβ) hβδ hδ1 hC hR henv
  obtain ⟨ρ, hρ, hρR, K, hK, henv⟩ := hlocal γ hγ hγ1
  refine ⟨ρ, hρ, hρR, K, hK, ?_⟩
  intro p x hp hx hregular
  obtain ⟨hbound, hdomain, hvalid⟩ := henv p x hp hx hregular
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hlimbound : Tendsto (fun n : ℕ => K * γ ^ n * ‖x‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using
      (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1)).mul_const ‖x‖
  have hnormlim : Tendsto (fun n => ‖bbCurrent rule G p x n‖) atTop (𝓝 0) :=
    squeeze_zero (fun n => norm_nonneg _) hbound hlimbound
  refine ⟨hbound, hdomain, hvalid, tendsto_zero_iff_norm_tendsto_zero.mpr hnormlim, ?_⟩
  have hroot : rootFactor (fun n => ‖bbCurrent rule G p x n‖) ≤ c := by
    apply le_of_forall_strict_upper_bound
    intro ε hcε
    obtain ⟨δ, hcδ, hδ⟩ := exists_between (lt_min hcε hc1)
    have hδ1 : δ < 1 := hδ.trans_le (min_le_right ε 1)
    have hδε : δ < ε := hδ.trans_le (min_le_left ε 1)
    have hδ0 : 0 < δ := hc.trans_lt hcδ
    obtain ⟨ρδ, hρδ, _hρδR, Kδ, hKδ, henvδ⟩ := hlocal δ hcδ hδ1
    have hsmall : ∀ᶠ n in atTop, ‖bbCurrent rule G p x n‖ < ρδ :=
      (tendsto_order.mp hnormlim).2 ρδ hρδ
    obtain ⟨k, hk⟩ := Filter.eventually_atTop.mp hsmall
    have hpδ : ‖bbPrevious rule G p x (k + 1)‖ ≤ ρδ := by
      rw [bbPrevious_succ]
      exact (hk k le_rfl).le
    have hxδ : ‖bbCurrent rule G p x (k + 1)‖ ≤ ρδ := (hk (k + 1) (by omega)).le
    have hregularδ : bbCurrent rule G p x (k + 1) = 0 ∨
        bbPrevious rule G p x (k + 1) ≠ bbCurrent rule G p x (k + 1) := by
      by_cases hz : bbCurrent rule G p x (k + 1) = 0
      · exact Or.inl hz
      · exact Or.inr (Ne.symm (sub_ne_zero.mp (hvalid (k + 1) hz).1))
    have htail := (henvδ (bbPrevious rule G p x (k + 1))
      (bbCurrent rule G p x (k + 1)) hpδ hxδ hregularδ).1
    let Cδ := Kδ * (‖bbCurrent rule G p x (k + 1)‖ + 1)
    have hCδ : 0 < Cδ := mul_pos (lt_of_lt_of_le zero_lt_one hKδ) (by positivity)
    have htailbound : ∀ n, ‖bbCurrent rule G p x (n + (k + 1))‖ ≤ Cδ * δ ^ n := by
      intro n
      rw [Nat.add_comm n, bbCurrent_add]
      apply (htail n).trans
      dsimp [Cδ]
      have hz := mul_nonneg (le_trans zero_le_one hKδ) (pow_nonneg hδ0.le n)
      nlinarith only [hz]
    have htailroot := rootFactor_le_of_envelope (fun n => ‖bbCurrent rule G p x (n + (k + 1))‖)
      (fun n => norm_nonneg _) δ hδ0.le ⟨Cδ, hCδ, htailbound⟩
    have htailbounded := rootTerm_bounded_of_eventual_envelope
      (fun n => ‖bbCurrent rule G p x (n + (k + 1))‖) (fun n => norm_nonneg _)
      Cδ δ hCδ hδ0.le (Filter.eventually_of_forall htailbound)
    exact ((rootFactor_le_shift (fun n => ‖bbCurrent rule G p x n‖)
      (fun n => norm_nonneg _) (k + 1) htailbounded).trans htailroot).trans hδε.le
  by_cases hx0 : x = 0
  · subst x
    have hz : (fun n => ‖bbCurrent rule G p 0 n‖ / ‖(0 : E)‖) = fun _ => (0 : ℝ) := by
      funext n
      simp only [norm_zero, div_zero]
    rw [hz, rootFactor_eq_zero_of_eventually_zero (fun _ => (0 : ℝ)) (Filter.eventually_of_forall (fun _ => rfl))]
    exact hc
  · have hbounded := rootTerm_bounded_of_eventual_envelope
      (fun n => ‖bbCurrent rule G p x n‖) (fun n => norm_nonneg _)
      (K * ‖x‖) γ (mul_pos hK0 (norm_pos_iff.mpr hx0)) hγ0.le
      (Filter.eventually_of_forall (fun n => by simpa only [mul_right_comm] using hbound n))
    rw [rootFactor_div_const (fun n => ‖bbCurrent rule G p x n‖)
      (fun n => norm_nonneg _) hbounded ‖x‖ (norm_pos_iff.mpr hx0)]
    exact hroot

end BB.Nonlinear
