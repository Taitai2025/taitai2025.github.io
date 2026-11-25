import Mathlib

/-!
Private companion to the Chinese research note, 2026-11-25.
Only finite scalar certificates are proved here. No assertion below formalizes
Darboux asymptotics, compactness, spectral decompositions, or cone projections.
-/
namespace RestartProjectedBB

open scoped BigOperators

/-- A strictly positive finite dual certificate forces a strictly positive
    restart criterion at at least one tested time. -/
theorem positive_dual_forces_trigger
    {m N : ℕ} (w : Fin m → ℝ) (ξ : Fin N → ℝ)
    (c : Fin N → Fin m → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hξ : ∀ k, 0 ≤ ξ k)
    (hdual : ∀ i, 0 < ∑ k, ξ k * c k i) :
    ∃ k, 0 < ∑ i, w i * c k i := by
  have hwpos : ∃ i, 0 < w i := by
    by_contra hn
    push_neg at hn
    have hle : (∑ i, w i) ≤ 0 := Finset.sum_nonpos (by
      intro i _
      exact hn i)
    linarith
  have hp : 0 < ∑ i, w i * (∑ k, ξ k * c k i) := by
    apply Finset.sum_pos'
    · intro i _
      exact mul_nonneg (hw i) (le_of_lt (hdual i))
    · obtain ⟨i, hi⟩ := hwpos
      exact ⟨i, Finset.mem_univ i, mul_pos hi (hdual i)⟩
  have heq : (∑ i, w i * (∑ k, ξ k * c k i)) =
      ∑ k, ξ k * (∑ i, w i * c k i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [heq] at hp
  by_contra hn
  push_neg at hn
  have hle : (∑ k, ξ k * (∑ i, w i * c k i)) ≤ 0 :=
    Finset.sum_nonpos (by
      intro k _
      exact mul_nonpos_of_nonneg_of_nonpos (hξ k) (hn k))
  linarith

/-- Final scalar contradiction after the spectral and projection identities
    have been established by the mathematical proof. -/
theorem projection_equality_contradiction
    (τ b vnormSq : ℝ) (hτ : 0 < τ) (hb : 0 < b)
    (hv : 0 < vnormSq) (horth : -(τ * b * vnormSq) = 0) : False := by
  have hp : 0 < τ * b * vnormSq := mul_pos (mul_pos hτ hb) hv
  linarith

/-- The pair maximum decreases after two steps from scalar norm inequalities.
    This does not establish the required projection or compactness facts. -/
theorem strict_two_step_max
    (u v w t : ℝ) (hvu : v ≤ u) (hwv : w < v) (htw : t ≤ w) :
    max w t < max u v := by
  rw [max_eq_left htw, max_eq_left hvu]
  exact lt_of_lt_of_le hwv hvu

/-- Rational residuals with precisely the indexing used in the note. -/
def residual (s : ℚ) : ℕ → ℚ
  | 0 => 1
  | 1 => s
  | n + 2 => s * (((2 * n + 3 : ℕ) : ℚ) * residual s (n + 1) -
      (n : ℚ) * residual s n) / ((n + 3 : ℕ) : ℚ)

def criterion (s : ℚ) (k : ℕ) : ℚ :=
  (1 - s) / s * residual s k * (residual s k - residual s (k - 1))

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem exact_dual_first :
    (criterion (1/2) 5 + 128 * criterion (1/2) 12) / 129 =
      (3409329 : ℚ) / 1477468749824 := by
  norm_num [criterion, residual]

theorem exact_dual_second :
    (criterion (9/10) 5 + 128 * criterion (9/10) 12) / 129 =
      (2366243076860328051781857 : ℚ) / 88064000000000000000000000000 := by
  norm_num [criterion, residual]

theorem exact_dual_positive :
    0 < (criterion (1/2) 5 + 128 * criterion (1/2) 12) / 129 ∧
    0 < (criterion (9/10) 5 + 128 * criterion (9/10) 12) / 129 := by
  rw [exact_dual_first, exact_dual_second]
  norm_num

def witnessCriterion (k : ℕ) : ℚ :=
  (criterion (1/2) k + criterion (9/10) k) / 2

theorem exact_no_earlier_trigger :
    ∀ k ∈ Finset.Icc 1 11, witnessCriterion k < 0 := by
  norm_num [Finset.mem_Icc]
  intro k hk1 hk11
  interval_cases k <;> norm_num [witnessCriterion, criterion, residual]

theorem exact_trigger_twelve : 0 < witnessCriterion 12 := by
  norm_num [witnessCriterion, criterion, residual]

theorem exact_modes_nonzero :
    ∀ k ∈ Finset.Icc 0 12, residual (1/2) k ≠ 0 ∧ residual (9/10) k ≠ 0 := by
  norm_num [Finset.mem_Icc]
  intro k hk12
  interval_cases k <;> norm_num [residual]

/-- Coordinate-level exact example; projection is represented by max(0,x).
    This is not a general theorem about orthogonal projection. -/
def hmul (x : ℚ × ℚ) : ℚ × ℚ := (x.1 - x.2, -x.1 + 4*x.2)
def dot (x y : ℚ × ℚ) : ℚ := x.1*y.1 + x.2*y.2
def orthant (x : ℚ × ℚ) : ℚ × ℚ := (max 0 x.1, max 0 x.2)

theorem exact_bb_example :
    let u : ℚ × ℚ := (3,1)
    let v := orthant (u - hmul u)
    let s := v-u
    let α := dot s s / dot s (hmul s)
    let w := orthant (v - (α * (hmul v).1, α * (hmul v).2))
    v = (1,0) ∧ α = 5/4 ∧ w = (0,5/4) ∧
    dot v v = 1 ∧ dot w w = 25/16 ∧
    dot v (hmul v) / 2 = 1/2 ∧ dot w (hmul w) / 2 = 25/8 := by
  norm_num [orthant, hmul, dot, Prod.mk_sub_mk]

#print axioms positive_dual_forces_trigger
#print axioms projection_equality_contradiction
#print axioms strict_two_step_max
#print axioms exact_dual_first
#print axioms exact_dual_second
#print axioms exact_dual_positive
#print axioms exact_no_earlier_trigger
#print axioms exact_trigger_twelve
#print axioms exact_modes_nonzero
#print axioms exact_bb_example
end RestartProjectedBB
