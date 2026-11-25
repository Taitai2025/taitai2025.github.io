import BB.Gluing
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Boundary handoff and finite termination

The first theorem turns two uniformly contracting invariant faces into a
single fixed block length.  The second handles the one-eigenvalue base.
These are mathematical lemmas with explicit dynamical hypotheses.
-/

namespace BB.Gluing

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_boundary_length {S : W → E → E}
    {C C₁ C₂ : Set E} {P : E → ℝ} {B K₁ K₂ r₁ r₂ : ℝ}
    (hB : 1 ≤ B) (hK₁ : 1 ≤ K₁) (hK₂ : 1 ≤ K₂)
    (hr₁ : 0 ≤ r₁) (hr₁' : r₁ < 1) (hr₂ : 0 ≤ r₂) (hr₂' : r₂ < 1)
    (hfirst : ∀ w z, z ∈ C → ‖S w z‖ ≤ B * ‖z‖)
    (hhandoff : ∀ w z, z ∈ C → P z = 0 → S w z ∈ C₁ ∪ C₂)
    (hchild₁ : ∀ l : List W, ∀ z ∈ C₁,
      ‖run S l z‖ ≤ K₁ * r₁^l.length * ‖z‖)
    (hchild₂ : ∀ l : List W, ∀ z ∈ C₂,
      ‖run S l z‖ ≤ K₂ * r₂^l.length * ‖z‖) :
    ∃ N : ℕ, 3 ≤ N ∧ ∀ l : List W, l.length = N → ∀ z ∈ C,
      P z = 0 → ‖run S l z‖ ≤ (1/2 : ℝ) * ‖z‖ := by
  let K := max K₁ K₂
  let r := max r₁ r₂
  have hK : 1 ≤ K := hK₁.trans (le_max_left _ _)
  have hr : 0 ≤ r := hr₁.trans (le_max_left _ _)
  have hr' : r < 1 := max_lt hr₁' hr₂'
  have hBK : 0 < 2 * B * K := by positivity
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (one_div_pos.mpr hBK) hr'
  refine ⟨m+3, by omega, ?_⟩
  intro l hl z hz hp
  cases l with
  | nil => simp at hl
  | cons w l =>
    have hlen : l.length = m+2 := by simp only [List.length_cons] at hl; omega
    have hpow : r^l.length ≤ r^m := pow_le_pow_of_le_one hr hr'.le (by omega)
    have hcoeff : B * K * r^l.length ≤ (1/2 : ℝ) := by
      have hh := mul_lt_mul_of_pos_left (lt_of_le_of_lt hpow hm) hBK
      have hid : (2 * B * K) * (1 / (2 * B * K)) = 1 := by field_simp
      rw [hid] at hh
      nlinarith
    have htail : ‖run S l (S w z)‖ ≤ K * r^l.length * ‖S w z‖ := by
      rcases hhandoff w z hz hp with hh | hh
      · have hc := hchild₁ l (S w z) hh
        have hpw : r₁^l.length ≤ r^l.length :=
          pow_le_pow_left hr₁ (le_max_left _ _) _
        have hmul : K₁ * r₁^l.length ≤ K * r^l.length :=
          mul_le_mul (le_max_left _ _) hpw (pow_nonneg hr₁ _) (by linarith)
        exact hc.trans (mul_le_mul_of_nonneg_right hmul (norm_nonneg _))
      · have hc := hchild₂ l (S w z) hh
        have hpw : r₂^l.length ≤ r^l.length :=
          pow_le_pow_left hr₂ (le_max_right _ _) _
        have hmul : K₂ * r₂^l.length ≤ K * r^l.length :=
          mul_le_mul (le_max_right _ _) hpw (pow_nonneg hr₂ _) (by linarith)
        exact hc.trans (mul_le_mul_of_nonneg_right hmul (norm_nonneg _))
    calc
      ‖run S (w :: l) z‖ ≤ K * r^l.length * ‖S w z‖ := htail
      _ ≤ K * r^l.length * (B * ‖z‖) :=
        mul_le_mul_of_nonneg_left (hfirst w z hz) (by positivity)
      _ = (B * K * r^l.length) * ‖z‖ := by ring
      _ ≤ (1/2 : ℝ) * ‖z‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg _)

theorem two_step_nilpotent_rate {S : W → E → E} {C : Set E} {B r : ℝ}
    (hr : 0 < r)
    (hzero : ∀ w, S w 0 = 0)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ B * ‖z‖)
    (hnil : ∀ w w' z, z ∈ C → S w' (S w z) = 0)
    (l : List W) {z : E} (hz : z ∈ C) :
    ‖run S l z‖ ≤ max 1 (B/r) * r^l.length * ‖z‖ := by
  have hzeroRun : ∀ l : List W, run S l 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons w l ih => simpa [run_cons, hzero] using ih
  cases l with
  | nil =>
    simp only [run_nil, List.length_nil, pow_zero, mul_one]
    exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)
  | cons w l =>
    cases l with
    | nil =>
      simp only [run_cons, run_nil, List.length_cons, List.length_nil, zero_add, pow_one]
      have h : B ≤ max 1 (B/r) * r := by
        have hh := mul_le_mul_of_nonneg_right (le_max_right 1 (B/r)) hr.le
        have heq : B/r*r = B := div_mul_cancel₀ B hr.ne'
        rwa [heq] at hh
      exact (hbound w z hz).trans (mul_le_mul_of_nonneg_right h (norm_nonneg _))
    | cons w' l =>
      simp only [run_cons, hnil w w' z hz, hzeroRun, norm_zero]
      positivity

/-- Scaling each homogeneous map scales a word by the corresponding power. -/
theorem run_rescaled {T : W → E → E} {C : Set E} {t : ℝ}
    (ht : 0 ≤ t) (hT : ∀ w z, z ∈ C → T w z ∈ C)
    (hscale : ∀ z ∈ C, ∀ s : ℝ, 0 ≤ s → s • z ∈ C)
    (hhom : ∀ w z, z ∈ C → ∀ s : ℝ, 0 ≤ s → T w (s • z) = s • T w z)
    (l : List W) {z : E} (hz : z ∈ C) :
    run (fun w z => t • T w z) l z = t^l.length • run T l z := by
  induction l generalizing z with
  | nil => simp
  | cons w l ih =>
    simp only [run_cons]
    rw [ih (hscale (T w z) (hT w z hz) t ht),
      run_homogeneous hT hhom l (hT w z hz) ht]
    rw [smul_smul]
    simp only [List.length_cons, pow_succ]

end BB.Gluing
