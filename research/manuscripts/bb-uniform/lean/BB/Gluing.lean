import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic

/-!
# Finite-horizon gluing for a family of homogeneous maps

This file formalizes the analytic/combinatorial core of the induction in
Section 3.  The hypotheses are explicit: in particular the boundary
contraction, the boundary deletion estimate and the one-step estimates
are inputs here, not asserted facts about a matrix without proof.
-/

namespace BB.Gluing

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Apply a finite word of maps in chronological order. -/
def run (S : W → E → E) : List W → E → E
  | [], z => z
  | w :: l, z => run S l (S w z)

@[simp] theorem run_nil (S : W → E → E) (z : E) : run S [] z = z := rfl
@[simp] theorem run_cons (S : W → E → E) (w : W) (l : List W) (z : E) :
    run S (w :: l) z = run S l (S w z) := rfl

theorem run_append (S : W → E → E) (l m : List W) (z : E) :
    run S (l ++ m) z = run S m (run S l z) := by
  induction l generalizing z with
  | nil => rfl
  | cons w l ih => simpa using ih (S w z)

theorem run_mem {S : W → E → E} {C : Set E}
    (hS : ∀ w z, z ∈ C → S w z ∈ C) (l : List W) {z : E} (hz : z ∈ C) :
    run S l z ∈ C := by
  induction l generalizing z with
  | nil => exact hz
  | cons w l ih => exact ih (hS w z hz)

theorem run_norm_bound {S : W → E → E} {C : Set E} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (l : List W) {z : E} (hz : z ∈ C) :
    ‖run S l z‖ ≤ Λ ^ l.length * ‖z‖ := by
  induction l generalizing z with
  | nil => simp
  | cons w l ih =>
    calc
      ‖run S (w :: l) z‖ ≤ Λ ^ l.length * ‖S w z‖ := ih (hS w z hz)
      _ ≤ Λ ^ l.length * (Λ * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hbound w z hz) (pow_nonneg hΛ _)
      _ = Λ ^ (w :: l).length * ‖z‖ := by simp [pow_succ]; ring

theorem run_lipschitz {S : W → E → E} {C : Set E} {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hLip : ∀ w x y, x ∈ C → y ∈ C → ‖S w x - S w y‖ ≤ Λ * ‖x-y‖)
    (l : List W) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    ‖run S l x - run S l y‖ ≤ Λ ^ l.length * ‖x-y‖ := by
  induction l generalizing x y with
  | nil => simp
  | cons w l ih =>
    calc
      ‖run S (w :: l) x - run S (w :: l) y‖ ≤
          Λ ^ l.length * ‖S w x - S w y‖ := ih (hS w x hx) (hS w y hy)
      _ ≤ Λ ^ l.length * (Λ * ‖x-y‖) :=
        mul_le_mul_of_nonneg_left (hLip w x y hx hy) (pow_nonneg hΛ _)
      _ = Λ ^ (w :: l).length * ‖x-y‖ := by simp [pow_succ]; ring

/-- Boundary contraction extended to all states using a controlled deletion. -/
theorem block_bound {S : W → E → E} {C : Set E} {P : E → ℝ}
    {Λ : ℝ} {N : ℕ}
    (hΛ : 0 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hLip : ∀ w x y, x ∈ C → y ∈ C → ‖S w x - S w y‖ ≤ Λ * ‖x-y‖)
    (hboundary : ∀ l : List W, l.length = N → ∀ z ∈ C,
      P z = 0 → ‖run S l z‖ ≤ (1/2 : ℝ) * ‖z‖)
    (hdelete : ∀ z ∈ C, ∃ z' ∈ C,
      P z' = 0 ∧ ‖z'‖ ≤ ‖z‖ ∧ ‖z-z'‖ ≤ P z)
    (l : List W) (hl : l.length = N) {z : E} (hz : z ∈ C) :
    ‖run S l z‖ ≤ (1/2 : ℝ) * ‖z‖ + Λ ^ N * P z := by
  obtain ⟨z', hz', hP, hnorm, hdist⟩ := hdelete z hz
  have h1 := run_lipschitz hΛ hS hLip l hz hz'
  rw [hl] at h1
  have h2 := hboundary l hl z' hz' hP
  have h3 : ‖run S l z‖ ≤ ‖run S l z - run S l z'‖ + ‖run S l z'‖ :=
    by simpa only [sub_add_cancel] using
      norm_add_le (run S l z - run S l z') (run S l z')
  have h4 := mul_le_mul_of_nonneg_left hdist (pow_nonneg hΛ N)
  linarith

noncomputable def Q (A : ℝ) (P : E → ℝ) (z : E) : ℝ := max ‖z‖ (A * P z)

theorem half_add_le_max (x y : ℝ) : (1/2 : ℝ)*x + (1/2 : ℝ)*y ≤ max x y := by
  have h1 := le_max_left x y
  have h2 := le_max_right x y
  linarith

theorem block_le_Q {S : W → E → E} {P : E → ℝ} {Λ : ℝ} {N : ℕ}
    {l : List W} {z : E}
    (h : ‖run S l z‖ ≤ (1/2 : ℝ) * ‖z‖ + Λ ^ N * P z) :
    ‖run S l z‖ ≤ Q (2 * Λ^N) P z := by
  unfold Q
  calc
    ‖run S l z‖ ≤ (1/2 : ℝ) * ‖z‖ + Λ ^ N * P z := h
    _ = (1/2 : ℝ) * ‖z‖ + (1/2 : ℝ) * (2 * Λ^N * P z) := by ring
    _ ≤ max ‖z‖ (2 * Λ^N * P z) := half_add_le_max _ _

def horizonValues (S : W → E → E) (N : ℕ) (z : E) : Set ℝ :=
  {r | ∃ l : List W, l.length < N ∧ r = ‖run S l z‖}

noncomputable def horizon (S : W → E → E) (N : ℕ) (z : E) : ℝ :=
  sSup (horizonValues S N z)

theorem horizonValues_nonempty (S : W → E → E) {N : ℕ} (hN : 0 < N) (z : E) :
    (horizonValues S N z).Nonempty :=
  ⟨‖z‖, [], hN, rfl⟩

theorem horizonValues_bdd {S : W → E → E} {C : Set E} {Λ : ℝ} {N : ℕ}
    (hΛ : 1 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    {z : E} (hz : z ∈ C) : BddAbove (horizonValues S N z) := by
  refine ⟨Λ^N * ‖z‖, ?_⟩
  rintro r ⟨l, hl, rfl⟩
  exact (run_norm_bound (by linarith) hS hbound l hz).trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right hΛ (Nat.le_of_lt hl)) (norm_nonneg _))

theorem norm_le_horizon {S : W → E → E} {N : ℕ} {z : E}
    (hN : 0 < N) (hb : BddAbove (horizonValues S N z)) :
    ‖z‖ ≤ horizon S N z :=
  le_csSup hb ⟨[], hN, rfl⟩

theorem run_le_horizon {S : W → E → E} {N : ℕ} {z : E}
    (hb : BddAbove (horizonValues S N z)) (l : List W) (hl : l.length < N) :
    ‖run S l z‖ ≤ horizon S N z :=
  le_csSup hb ⟨l, hl, rfl⟩

theorem horizon_le {S : W → E → E} {N : ℕ} {z : E} {b : ℝ}
    (hN : 0 < N) (h : ∀ l : List W, l.length < N → ‖run S l z‖ ≤ b) :
    horizon S N z ≤ b := by
  apply csSup_le (horizonValues_nonempty S hN z)
  rintro r ⟨l, hl, rfl⟩
  exact h l hl

/-- The finite-horizon common Lyapunov candidate from equation (3.13). -/
noncomputable def V (S : W → E → E) (N : ℕ) (A : ℝ) (P : E → ℝ) (z : E) : ℝ :=
  max (Q A P z) (horizon S N z)

theorem norm_le_V (S : W → E → E) (N : ℕ) (A : ℝ) (P : E → ℝ) (z : E) :
    ‖z‖ ≤ V S N A P z :=
  (le_max_left _ _).trans (le_max_left _ _)

theorem V_nonneg (S : W → E → E) (N : ℕ) (A : ℝ) (P : E → ℝ) (z : E) :
    0 ≤ V S N A P z := (norm_nonneg _).trans (norm_le_V S N A P z)

theorem V_upper {S : W → E → E} {C : Set E} {P : E → ℝ} {Λ : ℝ} {N : ℕ}
    (hN : 0 < N) (hΛ : 1 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hP : ∀ z ∈ C, P z ≤ ‖z‖) {z : E} (hz : z ∈ C) :
    V S N (2 * Λ^N) P z ≤ (2 * Λ^N) * ‖z‖ := by
  have hp : 1 ≤ Λ^N := one_le_pow_of_one_le hΛ N
  have hA : 0 ≤ 2 * Λ^N := by positivity
  apply max_le
  · apply max_le
    · nlinarith [norm_nonneg z]
    · exact mul_le_mul_of_nonneg_left (hP z hz) hA
  · apply horizon_le hN
    intro l hl
    have h := run_norm_bound (show 0 ≤ Λ by linarith) hS hbound l hz
    have hp' := pow_le_pow_right hΛ (Nat.le_of_lt hl)
    have := mul_le_mul_of_nonneg_right hp' (norm_nonneg z)
    nlinarith [norm_nonneg z]

/-- The finite-horizon candidate decreases under every map of the family. -/
theorem V_step {S : W → E → E} {C : Set E} {P : E → ℝ}
    {Λ A : ℝ} {N : ℕ}
    (hN : 1 < N) (hΛ : 1 ≤ Λ) (hA : 0 ≤ A)
    (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hP : ∀ w z, z ∈ C → P (S w z) ≤ P z)
    (hblock : ∀ l : List W, l.length = N → ∀ z ∈ C, ‖run S l z‖ ≤ Q A P z)
    (w : W) {z : E} (hz : z ∈ C) :
    V S N A P (S w z) ≤ V S N A P z := by
  have hb := horizonValues_bdd (N := N) hΛ hS hbound hz
  have hq : Q A P z ≤ V S N A P z := le_max_left _ _
  have hh : horizon S N z ≤ V S N A P z := le_max_right _ _
  apply max_le
  · apply max_le
    · exact (run_le_horizon hb [w] hN).trans hh
    · exact (mul_le_mul_of_nonneg_left (hP w z hz) hA).trans
        ((le_max_right _ _).trans hq)
  · apply horizon_le (by omega)
    intro l hl
    by_cases hlt : (w :: l).length < N
    · exact (run_le_horizon hb (w :: l) hlt).trans hh
    · have heq : (w :: l).length = N := by simp only [List.length_cons] at *; omega
      exact (hblock (w :: l) heq z hz).trans hq

theorem horizon_lipschitz {S : W → E → E} {C : Set E} {Λ : ℝ} {N : ℕ}
    (hN : 0 < N) (hΛ : 1 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hLip : ∀ w x y, x ∈ C → y ∈ C → ‖S w x - S w y‖ ≤ Λ * ‖x-y‖)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    |horizon S N x - horizon S N y| ≤ Λ^N * ‖x-y‖ := by
  have directional : ∀ x y, x ∈ C → y ∈ C →
      horizon S N x ≤ horizon S N y + Λ^N * ‖x-y‖ := by
    intro x y hx hy
    apply horizon_le hN
    intro l hl
    have hb := horizonValues_bdd (N := N) hΛ hS hbound hy
    have hr := run_le_horizon hb l hl
    have hd := run_lipschitz (show 0 ≤ Λ by linarith) hS hLip l hx hy
    have hp := mul_le_mul_of_nonneg_right
      (pow_le_pow_right hΛ (Nat.le_of_lt hl)) (norm_nonneg (x-y))
    have ht : ‖run S l x‖ ≤ ‖run S l x - run S l y‖ + ‖run S l y‖ :=
      by simpa only [sub_add_cancel] using
        norm_add_le (run S l x - run S l y) (run S l y)
    linarith
  have hxy := directional x y hx hy
  have hyx := directional y x hy hx
  rw [norm_sub_rev] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem V_lipschitz {S : W → E → E} {C : Set E} {P : E → ℝ}
    {Λ A J : ℝ} {N : ℕ}
    (hN : 0 < N) (hΛ : 1 ≤ Λ) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hLip : ∀ w x y, x ∈ C → y ∈ C → ‖S w x - S w y‖ ≤ Λ * ‖x-y‖)
    (hQ : ∀ x y, x ∈ C → y ∈ C → |Q A P x - Q A P y| ≤ J * ‖x-y‖)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    |V S N A P x - V S N A P y| ≤ max J (Λ^N) * ‖x-y‖ := by
  have hq := hQ x y hx hy
  have hh := horizon_lipschitz hN hΛ hS hbound hLip hx hy
  have hq' : |Q A P x - Q A P y| ≤ max J (Λ^N) * ‖x-y‖ :=
    hq.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hh' : |horizon S N x - horizon S N y| ≤ max J (Λ^N) * ‖x-y‖ :=
    hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  rcases abs_le.mp hq' with ⟨hq1,hq2⟩
  rcases abs_le.mp hh' with ⟨hh1,hh2⟩
  apply abs_le.mpr
  constructor
  · have h : V S N A P y ≤ V S N A P x + max J (Λ^N) * ‖x-y‖ := by
      apply max_le
      · have := le_max_left (Q A P x) (horizon S N x); unfold V; linarith
      · have := le_max_right (Q A P x) (horizon S N x); unfold V; linarith
    linarith
  · have h : V S N A P x ≤ V S N A P y + max J (Λ^N) * ‖x-y‖ := by
      apply max_le
      · have := le_max_left (Q A P y) (horizon S N y); unfold V; linarith
      · have := le_max_right (Q A P y) (horizon S N y); unfold V; linarith
    linarith

theorem run_homogeneous {S : W → E → E} {C : Set E}
    (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hhom : ∀ w z, z ∈ C → ∀ t : ℝ, 0 ≤ t → S w (t • z) = t • S w z)
    (l : List W) {z : E} (hz : z ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    run S l (t • z) = t • run S l z := by
  induction l generalizing z with
  | nil => rfl
  | cons w l ih =>
    simp only [run_cons, hhom w z hz t ht]
    exact ih (hS w z hz)

theorem horizon_homogeneous {S : W → E → E} {C : Set E} {Λ : ℝ} {N : ℕ}
    (hN : 0 < N) (hΛ : 1 ≤ Λ)
    (hscale : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → t • z ∈ C)
    (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hhom : ∀ w z, z ∈ C → ∀ t : ℝ, 0 ≤ t → S w (t • z) = t • S w z)
    {z : E} (hz : z ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    horizon S N (t • z) = t * horizon S N z := by
  have hb := horizonValues_bdd (N := N) hΛ hS hbound hz
  have hbt := horizonValues_bdd (N := N) hΛ hS hbound (hscale z hz t ht)
  have hnorm : ∀ l : List W, ‖run S l (t • z)‖ = t * ‖run S l z‖ := by
    intro l
    rw [run_homogeneous hS hhom l hz ht, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  apply le_antisymm
  · apply horizon_le hN
    intro l hl
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left (run_le_horizon hb l hl) ht
  · rcases eq_or_lt_of_le ht with ht0 | htpos
    · subst t
      simp only [zero_smul] at hbt
      simpa using (norm_nonneg (0 : E)).trans (norm_le_horizon hN hbt)
    · have h : horizon S N z ≤ horizon S N (t • z) / t := by
        apply horizon_le hN
        intro l hl
        apply (le_div_iff htpos).mpr
        have hh := run_le_horizon hbt l hl
        rw [hnorm] at hh
        simpa only [mul_comm] using hh
      have hh := (le_div_iff htpos).mp h
      simpa only [mul_comm] using hh

theorem Q_homogeneous {P : E → ℝ} {A t : ℝ} {z : E}
    (ht : 0 ≤ t) (hP : P (t • z) = t * P z) :
    Q A P (t • z) = t * Q A P z := by
  unfold Q
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht, hP,
    mul_max_of_nonneg _ _ ht]
  congr 1
  ring

theorem V_homogeneous {S : W → E → E} {C : Set E} {P : E → ℝ}
    {Λ A : ℝ} {N : ℕ}
    (hN : 0 < N) (hΛ : 1 ≤ Λ)
    (hscale : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → t • z ∈ C)
    (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hhom : ∀ w z, z ∈ C → ∀ t : ℝ, 0 ≤ t → S w (t • z) = t • S w z)
    (hPhom : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → P (t • z) = t * P z)
    {z : E} (hz : z ∈ C) {t : ℝ} (ht : 0 ≤ t) :
    V S N A P (t • z) = t * V S N A P z := by
  unfold V
  rw [Q_homogeneous ht (hPhom z hz t ht),
    horizon_homogeneous hN hΛ hscale hS hbound hhom hz ht,
    mul_max_of_nonneg _ _ ht]

/-- Undo the rescaling, using positive homogeneity of the common function. -/
theorem unscale_step {T S : W → E → E} {C : Set E} {v : E → ℝ} {c : ℝ}
    (hc : 0 ≤ c) (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hscale : ∀ w z, z ∈ C → T w z = c • S w z)
    (hhom : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → v (t • z) = t * v z)
    (hdecrease : ∀ w z, z ∈ C → v (S w z) ≤ v z)
    (w : W) {z : E} (hz : z ∈ C) : v (T w z) ≤ c * v z := by
  rw [hscale w z hz, hhom (S w z) (hS w z hz) c hc]
  exact mul_le_mul_of_nonneg_left (hdecrease w z hz) hc

/-- Iteration of a one-step Lyapunov estimate for a genuinely arbitrary sequence. -/
theorem trajectory_bound {T : W → E → E} {C : Set E} {v : E → ℝ}
    {c K : ℝ} (hc : 0 ≤ c)
    (hlower : ∀ z ∈ C, ‖z‖ ≤ v z)
    (hupper : ∀ z ∈ C, v z ≤ K * ‖z‖)
    (hstep : ∀ w z, z ∈ C → v (T w z) ≤ c * v z)
    (z : ℕ → E) (w : ℕ → W) (hz : ∀ k, z k ∈ C)
    (hrec : ∀ k, z (k+1) = T (w k) (z k)) (k : ℕ) :
    ‖z k‖ ≤ K * c^k * ‖z 0‖ := by
  have h : ∀ n, v (z n) ≤ c^n * v (z 0) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [hrec n]
      calc
        v (T (w n) (z n)) ≤ c * v (z n) := hstep (w n) (z n) (hz n)
        _ ≤ c * (c^n * v (z 0)) := mul_le_mul_of_nonneg_left ih hc
        _ = c^(n+1) * v (z 0) := by rw [pow_succ]; ring
  calc
    ‖z k‖ ≤ v (z k) := hlower _ (hz k)
    _ ≤ c^k * v (z 0) := h k
    _ ≤ c^k * (K * ‖z 0‖) := mul_le_mul_of_nonneg_left (hupper _ (hz 0)) (pow_nonneg hc _)
    _ = K * c^k * ‖z 0‖ := by ring

end BB.Gluing
