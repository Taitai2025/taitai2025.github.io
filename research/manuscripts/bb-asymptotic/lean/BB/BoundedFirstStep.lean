import BB.NonlinearUniversal

/-!
# A compact set of arbitrary positive first steps

The first step below is prescribed externally. All subsequent steps are the
actual BB secant rule, with its incoming secant retained. The compact set of
first steps may be wider than the Rayleigh-quotient interval.
-/

noncomputable section
namespace BB.Nonlinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def externalFirstOrbit (rule : Rule) (A : E →L[ℝ] E) (α : ℝ) (x : E) : ℕ → E
  | 0 => x
  | n + 1 => bbCurrent rule A x (x - α • A x) n

@[simp] theorem externalFirstOrbit_zero (rule : Rule) (A : E →L[ℝ] E) (α : ℝ) (x : E) :
    externalFirstOrbit rule A α x 0 = x := rfl

@[simp] theorem externalFirstOrbit_one (rule : Rule) (A : E →L[ℝ] E) (α : ℝ) (x : E) :
    externalFirstOrbit rule A α x 1 = x - α • A x := rfl

theorem externalFirstOrbit_zero_initial (rule : Rule) (A : E →L[ℝ] E) (α : ℝ) :
    ∀ n, externalFirstOrbit rule A α 0 n = 0 := by
  intro n
  cases n with
  | zero => rfl
  | succ n =>
    simp only [externalFirstOrbit, map_zero, smul_zero, sub_self,
      bbCurrent_zero_initial rule A (map_zero A)]

theorem externalFirstOrbit_update (rule : Rule) (A : E →L[ℝ] E) (α : ℝ)
    (x : E) (n : ℕ) :
    externalFirstOrbit rule A α x (n + 2) =
      externalFirstOrbit rule A α x (n + 1) -
        frozenQuotient rule A (externalFirstOrbit rule A α x (n + 1) -
          externalFirstOrbit rule A α x n) •
          A (externalFirstOrbit rule A α x (n + 1)) := by
  have hp : bbPrevious rule A x (x - α • A x) n = externalFirstOrbit rule A α x n := by
    cases n <;> rfl
  change bbCurrent rule A x (x - α • A x) (n + 1) = _
  rw [bbCurrent_succ, quadratic_bbStep, hp]
  rfl

theorem PositiveModel.externalFirst_distinct {A : E →L[ℝ] E} {m M : ℝ}
    (h : PositiveModel A m M) (α : ℝ) (hα : 0 < α) (x : E) (hx : x ≠ 0) :
    x ≠ x - α • A x := by
  intro he
  have hz : α • A x = 0 := by
    have hz' := sub_eq_self.mp he.symm
    exact hz'
  exact smul_ne_zero hα.ne' (h.map_ne_zero hx) hz

theorem PositiveModel.externalFirst_positive_steps {A : E →L[ℝ] E} {m M : ℝ}
    (h : PositiveModel A m M) (rule : Rule) (α : ℝ) (hα : 0 < α)
    (x : E) (hx : x ≠ 0) (n : ℕ)
    (hn : externalFirstOrbit rule A α x (n + 1) ≠ 0) :
    0 < frozenQuotient rule A (externalFirstOrbit rule A α x (n + 1) -
      externalFirstOrbit rule A α x n) := by
  have hp : bbPrevious rule A x (x - α • A x) n = externalFirstOrbit rule A α x n := by
    cases n <;> rfl
  have hs := h.quadratic_regular rule x (x - α • A x)
    (h.externalFirst_distinct α hα x hx) n hn
  have hb := h.frozen_interval rule _ hs
  rw [hp] at hb
  exact (one_div_pos.mpr h.M_pos).trans_le hb.1

/-- Source proposition `prop:bounded-first-step-envelope`, with a genuine
externally prescribed first step in an arbitrary compact positive set. -/
theorem bounded_first_step_envelope (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (rule : Rule) (m M β : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M * ‖z‖ ^ 2)
    (hβ : rate m M < β) (J : Set ℝ) (hJ : IsCompact J)
    (hJpos : ∀ α ∈ J, 0 < α) :
    ∃ K ≥ 1, ∀ α ∈ J, ∀ x : E, ∀ n,
      ‖externalFirstOrbit rule A α x n‖ ≤ K * β ^ n * ‖x‖ := by
  have hmodel := positiveModel_of_order_bounds A hA m M hm hmM hbounds
  have hβpos : 0 < β := (div_nonneg (sub_nonneg.mpr hmM) (by linarith)).trans_lt hβ
  obtain ⟨C, hC, henv⟩ := hilbert_frozen_envelope A hA rule m M β hm hmM hbounds hβ
  obtain ⟨L₀, hL₀⟩ := hJ.bddAbove
  let L : ℝ := max L₀ 0
  have hL : 0 ≤ L := le_max_right _ _
  refine ⟨max 1 (C * (1 + L * M) / β), le_max_left _ _, ?_⟩
  intro α hαJ x n
  have hα : 0 < α := hJpos α hαJ
  have hαL : α ≤ L := (hL₀ hαJ).trans (le_max_left _ _)
  have hfirst : ‖x - α • A x‖ ≤ (1 + L * M) * ‖x‖ := by
    calc
      ‖x - α • A x‖ ≤ ‖x‖ + ‖α • A x‖ := norm_sub_le _ _
      _ = ‖x‖ + α * ‖A x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα]
      _ ≤ ‖x‖ + L * (M * ‖x‖) := add_le_add_left
        (mul_le_mul hαL (hmodel.norm_upper x) (norm_nonneg _) hL) _
      _ = (1 + L * M) * ‖x‖ := by ring
  by_cases hx : x = 0
  · subst x
    rw [externalFirstOrbit_zero_initial]
    simp
  · cases n with
    | zero =>
      simpa only [externalFirstOrbit_zero, pow_zero, mul_one, one_mul] using
        mul_le_mul_of_nonneg_right
          (le_max_left 1 (C * (1 + L * M) / β)) (norm_nonneg x)
    | succ n =>
      change ‖bbCurrent rule A x (x - α • A x) n‖ ≤ _
      calc
        _ ≤ C * β ^ n * ‖x - α • A x‖ :=
          henv x (x - α • A x) (hmodel.externalFirst_distinct α hα x hx) n
        _ ≤ C * β ^ n * ((1 + L * M) * ‖x‖) :=
          mul_le_mul_of_nonneg_left hfirst (mul_nonneg (by linarith) (pow_nonneg hβpos.le n))
        _ = (C * (1 + L * M) / β) * β ^ (n + 1) * ‖x‖ := by
          rw [pow_succ]
          field_simp
          ring
        _ ≤ max 1 (C * (1 + L * M) / β) * β ^ (n + 1) * ‖x‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hβpos.le _))
            (norm_nonneg x)

end BB.Nonlinear
