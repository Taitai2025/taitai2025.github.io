import BB.Nonlinear

/-!
# Actual BB trajectories and finite-horizon comparison

The trajectories below are total functions.  The theorems prove positivity of
all quotients evaluated before termination, so totalization at a zero secant is
never used on a nonterminal local trajectory.
-/

noncomputable section

namespace BB.Nonlinear

open scoped Topology

inductive Rule where
  | long
  | short
  deriving DecidableEq

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- One fixed choice of the two classical BB secant quotients. -/
def Rule.quotient (rule : Rule) (s y : E) : ℝ :=
  match rule with
  | .long => bb1 s y
  | .short => bb2 s y

/-- Explicit linear-model hypotheses supplied by the positive spectral bounds. -/
structure PositiveModel (A : E →L[ℝ] E) (m M : ℝ) : Prop where
  m_pos : 0 < m
  m_le_M : m ≤ M
  norm_upper : ∀ x, ‖A x‖ ≤ M * ‖x‖
  coercive : ∀ x, m * ‖x‖ ^ 2 ≤ inner (𝕜 := ℝ) x (A x)
  square_lower : ∀ x, m * inner (𝕜 := ℝ) x (A x) ≤ ‖A x‖ ^ 2
  square_upper : ∀ x, ‖A x‖ ^ 2 ≤ M * inner (𝕜 := ℝ) x (A x)

variable {A : E →L[ℝ] E} {m M : ℝ}

theorem PositiveModel.M_pos (h : PositiveModel A m M) : 0 < M := h.m_pos.trans_le h.m_le_M

theorem PositiveModel.norm_lower (h : PositiveModel A m M) (x : E) : m * ‖x‖ ≤ ‖A x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  · exact norm_lower_of_inner_lower x (A x) m hx (h.coercive x)

theorem PositiveModel.map_ne_zero (h : PositiveModel A m M) {x : E} (hx : x ≠ 0) : A x ≠ 0 := by
  have hn := (mul_pos h.m_pos (norm_pos_iff.mpr hx)).trans_le (h.norm_lower x)
  exact norm_pos_iff.mp hn

/-- Frozen secant quotient, with the selected rule kept fixed. -/
def frozenQuotient (rule : Rule) (A : E →L[ℝ] E) (s : E) : ℝ := rule.quotient s (A s)

theorem PositiveModel.frozen_interval (h : PositiveModel A m M) (rule : Rule) (s : E) (hs : s ≠ 0) :
    1 / M ≤ frozenQuotient rule A s ∧ frozenQuotient rule A s ≤ 1 / m := by
  have hb := frozen_steps_interval s (A s) m M hs h.m_pos h.m_le_M
    (h.coercive s) (inner_model_upper A M h.norm_upper s) (h.square_lower s) (h.square_upper s)
  cases rule with
  | long => exact ⟨hb.1, hb.2.1⟩
  | short => exact ⟨hb.2.2.1, hb.2.2.2⟩

/-- The constant in the common BB secant perturbation estimate. -/
def secantConstant (m M : ℝ) : ℝ := max (2 / m ^ 2) (14 * M ^ 2 / m ^ 4)

/-- A common directional Lipschitz constant, valid for both fixed rules. -/
def directionConstant (m M : ℝ) : ℝ := 2 * M / m ^ 2 + 2 * M ^ 3 / m ^ 4

theorem PositiveModel.secantConstant_pos (h : PositiveModel A m M) : 0 < secantConstant m M := by
  exact (div_pos (by norm_num) (sq_pos_of_pos h.m_pos)).trans_le (le_max_left _ _)

theorem PositiveModel.directionConstant_pos (h : PositiveModel A m M) : 0 < directionConstant m M := by
  dsimp [directionConstant]
  have hm := h.m_pos
  have hM := h.M_pos
  positivity

theorem PositiveModel.local_step (h : PositiveModel A m M) (rule : Rule)
    (s y : E) (ε : ℝ) (hs : s ≠ 0) (hε : 0 ≤ ε) (hεhalf : ε ≤ m / 2)
    (hr : ‖y - A s‖ ≤ ε * ‖s‖) :
    0 < rule.quotient s y ∧ rule.quotient s y ≤ 2 / m ∧
      |rule.quotient s y - frozenQuotient rule A s| ≤ secantConstant m M * ε := by
  have hεm : ε < m := by have hm := h.m_pos; linarith
  have hb := bb_step_bounds s y (A s) m M ε hs h.m_pos h.m_le_M hε hεm
    (h.coercive s) (inner_model_upper A M h.norm_upper s) (h.norm_upper s) hr
  have hp := common_secant_perturbation s y (A s) m M ε hs h.m_pos h.m_le_M hε hεhalf
    (h.coercive s) (h.norm_upper s) hr
  have hupper : 1 / (m - ε) ≤ 2 / m := by
    apply (div_le_div_iff (by linarith : 0 < m - ε) h.m_pos).mpr
    linarith
  cases rule with
  | long => exact ⟨hb.2.2.1, hb.2.2.2.2.2.1.trans hupper, hp.1⟩
  | short => exact ⟨hb.2.2.2.1, hb.2.2.2.2.2.2.2.trans hupper, hp.2⟩

theorem PositiveModel.direction_bound (h : PositiveModel A m M) (rule : Rule)
    (s t : E) (hs : s ≠ 0) (ht : t ≠ 0) :
    |frozenQuotient rule A s - frozenQuotient rule A t| ≤
      2 * directionConstant m M * ‖s - t‖ / min ‖s‖ ‖t‖ := by
  have hb := frozen_steps_lipschitz_min A m M h.m_pos h.M_pos.le h.norm_upper h.coercive s t hs ht
  cases rule with
  | short => exact hb.2
  | long =>
    apply hb.1.trans
    have hL : 2 * M / m ^ 2 ≤ directionConstant m M := by
      dsimp [directionConstant]
      have hm := h.m_pos
      have hM := h.M_pos
      exact le_add_of_nonneg_right (by positivity)
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by norm_num)) (norm_nonneg _))
      (le_of_lt (lt_min (norm_pos_iff.mpr hs) (norm_pos_iff.mpr ht)))

/-- The incoming secant and the current point are retained as the state. -/
def bbTransition (rule : Rule) (G : E → E) (z : E × E) : E × E :=
  (z.2, z.2 - rule.quotient (z.2 - z.1) (G z.2 - G z.1) • G z.2)

/-- Actual BB state after n updates, starting from (previous,current). -/
def bbState (rule : Rule) (G : E → E) (p x : E) : ℕ → E × E
  | 0 => (p, x)
  | n + 1 => bbTransition rule G (bbState rule G p x n)

def bbCurrent (rule : Rule) (G : E → E) (p x : E) (n : ℕ) : E := (bbState rule G p x n).2

def bbPrevious (rule : Rule) (G : E → E) (p x : E) (n : ℕ) : E := (bbState rule G p x n).1

def bbStep (rule : Rule) (G : E → E) (p x : E) (n : ℕ) : ℝ :=
  rule.quotient (bbCurrent rule G p x n - bbPrevious rule G p x n)
    (G (bbCurrent rule G p x n) - G (bbPrevious rule G p x n))

@[simp] theorem bbCurrent_zero (rule : Rule) (G : E → E) (p x : E) : bbCurrent rule G p x 0 = x := rfl
@[simp] theorem bbPrevious_zero (rule : Rule) (G : E → E) (p x : E) : bbPrevious rule G p x 0 = p := rfl
@[simp] theorem bbPrevious_succ (rule : Rule) (G : E → E) (p x : E) (n : ℕ) :
    bbPrevious rule G p x (n + 1) = bbCurrent rule G p x n := rfl

theorem bbCurrent_succ (rule : Rule) (G : E → E) (p x : E) (n : ℕ) :
    bbCurrent rule G p x (n + 1) = bbCurrent rule G p x n - bbStep rule G p x n • G (bbCurrent rule G p x n) := rfl

theorem bb_secant_succ (rule : Rule) (G : E → E) (p x : E) (n : ℕ) :
    bbCurrent rule G p x (n + 1) - bbPrevious rule G p x (n + 1) =
      -bbStep rule G p x n • G (bbCurrent rule G p x n) := by
  rw [bbCurrent_succ, bbPrevious_succ, neg_smul]
  abel

theorem bb_zero_next (rule : Rule) (G : E → E) (p x : E) (hG : G 0 = 0)
    (n : ℕ) (hz : bbCurrent rule G p x n = 0) : bbCurrent rule G p x (n + 1) = 0 := by
  rw [bbCurrent_succ, hz, hG, smul_zero, sub_self]

@[simp] theorem quadratic_bbStep (rule : Rule) (p x : E) (n : ℕ) :
    bbStep rule A p x n = frozenQuotient rule A (bbCurrent rule A p x n - bbPrevious rule A p x n) := by
  simp only [bbStep, frozenQuotient, map_sub]

/-- Every nonterminal quadratic state has a nonzero incoming secant. -/
theorem PositiveModel.quadratic_regular (h : PositiveModel A m M) (rule : Rule)
    (p x : E) (hpx : p ≠ x) : ∀ n, bbCurrent rule A p x n ≠ 0 →
      bbCurrent rule A p x n - bbPrevious rule A p x n ≠ 0 := by
  intro n
  induction n with
  | zero => intro _; exact sub_ne_zero.mpr (Ne.symm hpx)
  | succ n ih =>
    intro hn
    have hcur : bbCurrent rule A p x n ≠ 0 := by
      intro hz
      exact hn (bb_zero_next rule A p x (map_zero A) n hz)
    have hs := ih hcur
    have hb := h.frozen_interval rule _ hs
    have ha : 0 < bbStep rule A p x n := by
      rw [quadratic_bbStep]
      exact (one_div_pos.mpr h.M_pos).trans_le hb.1
    rw [bb_secant_succ]
    exact smul_ne_zero (neg_ne_zero.mpr ha.ne') (h.map_ne_zero hcur)

/-- A coarse one-step norm bound, avoiding any compactness assumption. -/
theorem PositiveModel.model_update_bound (h : PositiveModel A m M) (e : E) (α : ℝ)
    (ha : 0 ≤ α) (haM : α ≤ 1 / m) :
    ‖e - α • A e‖ ≤ (1 + M / m) * ‖e‖ := by
  calc
    ‖e - α • A e‖ ≤ ‖e‖ + ‖α • A e‖ := norm_sub_le _ _
    _ = ‖e‖ + α * ‖A e‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
    _ ≤ ‖e‖ + (1 / m) * (M * ‖e‖) :=
      add_le_add_left (mul_le_mul haM (h.norm_upper e) (norm_nonneg _) (one_div_pos.mpr h.m_pos).le) _
    _ = (1 + M / m) * ‖e‖ := by ring

/-- Uniform finite growth for the actual frozen BB trajectory. -/
theorem PositiveModel.quadratic_growth (h : PositiveModel A m M) (rule : Rule)
    (p x : E) (hpx : p ≠ x) : ∀ n,
      ‖bbCurrent rule A p x n‖ ≤ (1 + M / m) ^ n * ‖x‖ := by
  have hL : 0 ≤ 1 + M / m := by have hm := h.m_pos; have hM := h.M_pos; positivity
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    by_cases hz : bbCurrent rule A p x n = 0
    · rw [bb_zero_next rule A p x (map_zero A) n hz, norm_zero]
      positivity
    · have hs := h.quadratic_regular rule p x hpx n hz
      have hb := h.frozen_interval rule _ hs
      have ha : 0 ≤ bbStep rule A p x n := by
        rw [quadratic_bbStep]
        exact ((one_div_pos.mpr h.M_pos).trans_le hb.1).le
      have haM : bbStep rule A p x n ≤ 1 / m := by simpa only [quadratic_bbStep] using hb.2
      rw [bbCurrent_succ]
      calc
        _ ≤ (1 + M / m) * ‖bbCurrent rule A p x n‖ := h.model_update_bound _ _ ha haM
        _ ≤ (1 + M / m) * ((1 + M / m) ^ n * ‖x‖) := mul_le_mul_of_nonneg_left ih hL
        _ = (1 + M / m) ^ (n + 1) * ‖x‖ := by rw [pow_succ]; ring

/-- Difference of incoming secants in terms of the two endpoint errors. -/
theorem secant_difference_bound (e eHat p pHat : E) (δ R : ℝ)
    (he : ‖e - eHat‖ ≤ δ * R) (hp : ‖p - pHat‖ ≤ δ * R) :
    ‖(e - p) - (eHat - pHat)‖ ≤ 2 * δ * R := by
  have hid : (e - p) - (eHat - pHat) = (e - eHat) - (p - pHat) := by abel
  rw [hid]
  exact (norm_sub_le _ _).trans (by linarith only [he, hp])

/-- The frozen quotient remains quantitatively controlled under secant errors. -/
theorem PositiveModel.frozen_direction_error (h : PositiveModel A m M) (rule : Rule)
    (s t : E) (δ d R : ℝ) (hδ : 0 ≤ δ) (hd : 0 < d) (hR : 0 < R)
    (hδd : δ ≤ d / 4) (ht : d * R ≤ ‖t‖)
    (hst : ‖s - t‖ ≤ 2 * δ * R) :
    s ≠ 0 ∧ t ≠ 0 ∧ |frozenQuotient rule A s - frozenQuotient rule A t| ≤
      (8 * directionConstant m M / d) * δ := by
  have hdr : 0 < d * R / 2 := by positivity
  have hnorm : ‖t‖ - ‖s‖ ≤ ‖s - t‖ := by simpa [norm_sub_rev] using norm_sub_norm_le t s
  have hδR := mul_le_mul_of_nonneg_right hδd hR.le
  have hslo : d * R / 2 ≤ ‖s‖ := by nlinarith only [ht, hst, hnorm, hδR]
  have htlo : d * R / 2 ≤ ‖t‖ := by linarith only [ht, hdr]
  have hs0 : s ≠ 0 := norm_pos_iff.mp (hdr.trans_le hslo)
  have ht0 : t ≠ 0 := norm_pos_iff.mp ((mul_pos hd hR).trans_le ht)
  have hL := h.directionConstant_pos
  refine ⟨hs0, ht0, (h.direction_bound rule s t hs0 ht0).trans ?_⟩
  calc
    2 * directionConstant m M * ‖s - t‖ / min ‖s‖ ‖t‖
        ≤ (2 * directionConstant m M * (2 * δ * R)) / (d * R / 2) :=
      div_le_div (by positivity)
        (mul_le_mul_of_nonneg_left hst (by positivity)) hdr (le_min hslo htlo)
    _ = (8 * directionConstant m M / d) * δ := by
      field_simp [hd.ne', hR.ne']
      ring

/-- Quantitative one-step perturbation for the actual and frozen updates. -/
theorem PositiveModel.update_tracking_bound (h : PositiveModel A m M)
    (e eHat g : E) (α aHat δ Ω R C a0 : ℝ)
    (hδ : 0 ≤ δ) (hΩ : 0 ≤ Ω) (_hR : 0 ≤ R) (_hC : 0 ≤ C) (ha0 : 0 ≤ a0)
    (hα : 0 ≤ α) (hαup : α ≤ 2 / m) (haHat : 0 ≤ aHat) (haHatup : aHat ≤ 1 / m)
    (he : ‖e - eHat‖ ≤ δ * R) (henorm : ‖e‖ ≤ C * R)
    (hgrad : ‖g - A e‖ ≤ Ω * ‖e‖)
    (hstep : |α - aHat| ≤ a0 * δ + secantConstant m M * Ω) :
    ‖(e - α • g) - (eHat - aHat • A eHat)‖ ≤
      ((1 + M / m + a0 * M * C) * δ +
        C * (M * secantConstant m M + 2 / m) * Ω) * R := by
  have hm := h.m_pos
  have hM := h.M_pos
  have hsec := h.secantConstant_pos
  have hL : 0 ≤ 1 + M / m := by positivity
  have hsum : 0 ≤ a0 * δ + secantConstant m M * Ω := by positivity
  have hid := tracking_update_identity A e eHat (g - A e) α aHat
  have hg : A e + (g - A e) = g := by abel
  rw [hg] at hid
  rw [hid]
  have hmodel : ‖(e - eHat) - aHat • A (e - eHat)‖ ≤ (1 + M / m) * (δ * R) :=
    (h.model_update_bound _ _ haHat haHatup).trans (mul_le_mul_of_nonneg_left he hL)
  have hfirst : ‖(α - aHat) • A e‖ ≤
      (a0 * δ + secantConstant m M * Ω) * (M * (C * R)) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul hstep
      ((h.norm_upper e).trans (mul_le_mul_of_nonneg_left henorm hM.le)) (norm_nonneg _) hsum
  have hsecond : ‖α • (g - A e)‖ ≤ (2 / m) * (Ω * (C * R)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα]
    exact mul_le_mul hαup (hgrad.trans (mul_le_mul_of_nonneg_left henorm hΩ))
      (norm_nonneg _) (by positivity)
  calc
    _ ≤ ‖(e - eHat) - aHat • A (e - eHat)‖ + ‖(α - aHat) • A e‖ + ‖α • (g - A e)‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ (1 + M / m) * (δ * R) +
        (a0 * δ + secantConstant m M * Ω) * (M * (C * R)) +
        (2 / m) * (Ω * (C * R)) := add_le_add (add_le_add hmodel hfirst) hsecond
    _ = _ := by ring

/-- A local two-point estimate gives the current-point linearization error. -/
theorem current_remainder (G : E → E) (A : E →L[ℝ] E) (b Ω : ℝ)
    (hb : 0 ≤ b) (hG : G 0 = 0)
    (hrem : ∀ u, ‖u‖ ≤ b → ∀ v, ‖v‖ ≤ b → ‖G u - G v - A (u - v)‖ ≤ Ω * ‖u - v‖)
    (u : E) (hu : ‖u‖ ≤ b) : ‖G u - A u‖ ≤ Ω * ‖u‖ := by
  simpa [hG] using hrem u hu 0 (by simpa using hb)

/-- A nonzero point in the perturbation ball has nonzero gradient. -/
theorem PositiveModel.local_map_ne_zero (h : PositiveModel A m M)
    (G : E → E) (u : E) (Ω : ℝ) (hu : u ≠ 0) (hΩ : Ω < m)
    (hr : ‖G u - A u‖ ≤ Ω * ‖u‖) : G u ≠ 0 := by
  have hn := (secant_norm_bounds u (G u) (A u) m M Ω hu (h.coercive u)
    (inner_model_upper A M h.norm_upper u) (h.norm_upper u) hr).1
  exact norm_pos_iff.mp ((mul_pos (sub_pos.mpr hΩ) (norm_pos_iff.mpr hu)).trans_le hn)

/-- Explicit finite-horizon tracking for the actual BB recurrence.

The smallness condition is quantitative and is used to prove, rather than
assume, all nonterminal secants and gradients are nonzero and all steps positive.
-/
theorem PositiveModel.finite_tracking_explicit (h : PositiveModel A m M) (rule : Rule)
    (G : E → E) (p x : E) (N q : ℕ) (τ r Ω D S d : ℝ)
    (hτ : 0 < τ) (hr : 0 < r) (hΩ : 0 ≤ Ω) (hΩhalf : Ω ≤ m / 2)
    (hD : 1 ≤ D) (hDpow : (1 + M / m) ^ N ≤ D) (hS : 1 ≤ S)
    (hd : 0 < d) (hdeq : d = m * τ / M)
    (hSbound : (1 + M / m + (8 * directionConstant m M / d) * M * (D + 1)) +
      (D + 1) * (M * secantConstant m M + 2 / m) ≤ S)
    (hsmall : Ω * S ^ N ≤ min 1 (min (τ / 2) (d / 4)))
    (hG : G 0 = 0)
    (hrem : ∀ u, ‖u‖ ≤ (D + 1) * r → ∀ v, ‖v‖ ≤ (D + 1) * r →
      ‖G u - G v - A (u - v)‖ ≤ Ω * ‖u - v‖)
    (hp : ‖p‖ ≤ r) (hx : ‖x‖ ≤ r) (hpx : p ≠ x) (hx0 : x ≠ 0)
    (hqN : q ≤ N)
    (hpre : ∀ j < q, τ * ‖x‖ ≤ ‖bbCurrent rule A p x j‖) :
    (∀ j ≤ q, ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ ≤ Ω * S ^ j * ‖x‖ ∧
      ‖bbCurrent rule G p x j‖ + ‖bbCurrent rule A p x j‖ ≤ (2 * D + 1) * ‖x‖) ∧
    (∀ j < q, bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
      G (bbCurrent rule G p x j) ≠ 0 ∧ 0 < bbStep rule G p x j) := by
  have hm := h.m_pos
  have hM := h.M_pos
  have hR : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  have hC : 0 < D + 1 := by linarith
  have hL : 1 ≤ 1 + M / m := le_add_of_nonneg_right (div_nonneg hM.le hm.le)
  have hS0 : 0 ≤ S := by linarith
  have ha0 : 0 ≤ 8 * directionConstant m M / d := by have hdir := h.directionConstant_pos; positivity
  have hB : 0 ≤ (D + 1) * (M * secantConstant m M + 2 / m) := by
    have hsec := h.secantConstant_pos
    positivity
  have hΩm : Ω < m := by linarith
  have hball : 0 ≤ (D + 1) * r := by positivity
  have budget : ∀ j ≤ N, 0 ≤ Ω * S ^ j ∧ Ω * S ^ j ≤ 1 ∧
      Ω * S ^ j ≤ τ / 2 ∧ Ω * S ^ j ≤ d / 4 := by
    intro j hj
    have hpow : S ^ j ≤ S ^ N := pow_le_pow_right hS hj
    have hle := (mul_le_mul_of_nonneg_left hpow hΩ).trans hsmall
    exact ⟨mul_nonneg hΩ (pow_nonneg hS0 j), hle.trans (min_le_left _ _),
      (hle.trans (min_le_right _ _)).trans (min_le_left _ _),
      (hle.trans (min_le_right _ _)).trans (min_le_right _ _)⟩
  have frozenNorm : ∀ j ≤ N, ‖bbCurrent rule A p x j‖ ≤ D * ‖x‖ := by
    intro j hj
    exact (h.quadratic_growth rule p x hpx j).trans
      (mul_le_mul_of_nonneg_right ((pow_le_pow_right hL hj).trans hDpow) hR.le)
  have actualNorm : ∀ j ≤ N,
      ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ ≤ Ω * S ^ j * ‖x‖ →
      ‖bbCurrent rule G p x j‖ ≤ (D + 1) * ‖x‖ := by
    intro j hj he
    have ht := frozenNorm j hj
    have hb := mul_le_mul_of_nonneg_right (budget j hj).2.1 hR.le
    have hn : ‖bbCurrent rule G p x j‖ ≤
        ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ + ‖bbCurrent rule A p x j‖ :=
      by
        calc
          _ = ‖(bbCurrent rule G p x j - bbCurrent rule A p x j) + bbCurrent rule A p x j‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
    nlinarith only [hn, he, ht, hb]
  have induction_claim : ∀ n ≤ q,
      (∀ i ≤ n, ‖bbCurrent rule G p x i - bbCurrent rule A p x i‖ ≤ Ω * S ^ i * ‖x‖) ∧
      (∀ i < n, bbCurrent rule G p x i - bbPrevious rule G p x i ≠ 0 ∧
        G (bbCurrent rule G p x i) ≠ 0 ∧ 0 < bbStep rule G p x i) := by
    intro n
    induction n with
    | zero =>
      intro _
      refine ⟨?_, by intro i hi; omega⟩
      intro i hi
      have hiz : i = 0 := by omega
      subst i
      simp only [bbCurrent_zero, sub_self, norm_zero, pow_zero, mul_one]
      exact mul_nonneg hΩ hR.le
    | succ j ih =>
      intro hjq
      have hjq' : j < q := by omega
      have hjN : j ≤ N := by omega
      have old := ih (by omega)
      have δnonneg := (budget j hjN).1
      have δone := (budget j hjN).2.1
      have δtau := (budget j hjN).2.2.1
      have δd := (budget j hjN).2.2.2
      have herr := old.1 j le_rfl
      have hcurNorm := actualNorm j hjN herr
      have hcurBall : ‖bbCurrent rule G p x j‖ ≤ (D + 1) * r :=
        hcurNorm.trans (mul_le_mul_of_nonneg_left hx hC.le)
      have hprevBall : ‖bbPrevious rule G p x j‖ ≤ (D + 1) * r := by
        cases j with
        | zero =>
          simp only [bbPrevious_zero]
          exact hp.trans (by nlinarith only [hD, hr])
        | succ k =>
          rw [bbPrevious_succ]
          exact (actualNorm k (by omega) (old.1 k (by omega))).trans
            (mul_le_mul_of_nonneg_left hx hC.le)
      have hgradRem := current_remainder G A ((D + 1) * r) Ω hball hG hrem _ hcurBall
      have hhatCur : bbCurrent rule A p x j ≠ 0 :=
        norm_pos_iff.mp ((mul_pos hτ hR).trans_le (hpre j hjq'))
      have hhatSec := h.quadratic_regular rule p x hpx j hhatCur
      have hfrozen := h.frozen_interval rule _ hhatSec
      have haHat : 0 ≤ bbStep rule A p x j := by
        rw [quadratic_bbStep]
        exact ((one_div_pos.mpr hM).trans_le hfrozen.1).le
      have haHatup : bbStep rule A p x j ≤ 1 / m := by simpa only [quadratic_bbStep] using hfrozen.2
      have hsep : bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
          |frozenQuotient rule A (bbCurrent rule G p x j - bbPrevious rule G p x j) -
            frozenQuotient rule A (bbCurrent rule A p x j - bbPrevious rule A p x j)| ≤
              (8 * directionConstant m M / d) * (Ω * S ^ j) := by
        cases j with
        | zero =>
          simp only [bbCurrent_zero, bbPrevious_zero, sub_self, abs_zero]
          exact ⟨sub_ne_zero.mpr (Ne.symm hpx), mul_nonneg ha0 δnonneg⟩
        | succ k =>
          have hkq : k < q := by omega
          have hkhat : bbCurrent rule A p x k ≠ 0 :=
            norm_pos_iff.mp ((mul_pos hτ hR).trans_le (hpre k hkq))
          have hksec := h.quadratic_regular rule p x hpx k hkhat
          have hkinterval := h.frozen_interval rule _ hksec
          have hklower : 1 / M ≤ bbStep rule A p x k := by
            simpa only [quadratic_bbStep] using hkinterval.1
          have hgen := generated_secant_lower (bbCurrent rule A p x k) (A (bbCurrent rule A p x k))
            (bbStep rule A p x k) m M τ ‖x‖ hm hM hklower
            (h.norm_lower _) (hpre k hkq)
          have ht : d * ‖x‖ ≤ ‖bbCurrent rule A p x (k + 1) - bbPrevious rule A p x (k + 1)‖ := by
            rw [hdeq, bb_secant_succ]
            exact hgen
          have hpErr : ‖bbPrevious rule G p x (k + 1) - bbPrevious rule A p x (k + 1)‖ ≤
              (Ω * S ^ (k + 1)) * ‖x‖ := by
            rw [bbPrevious_succ, bbPrevious_succ]
            exact (old.1 k (by omega)).trans (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (pow_le_pow_right hS (by omega : k ≤ k + 1)) hΩ) hR.le)
          have hst := secant_difference_bound _ _ _ _ (Ω * S ^ (k + 1)) ‖x‖ herr hpErr
          have hdirection := h.frozen_direction_error rule _ _ (Ω * S ^ (k + 1)) d ‖x‖
            δnonneg hd hR δd ht hst
          exact ⟨hdirection.1, hdirection.2.2⟩
      have hrsec := hrem _ hcurBall _ hprevBall
      have hlocal := h.local_step rule _ _ Ω hsep.1 hΩ hΩhalf hrsec
      have hapos : 0 < bbStep rule G p x j := hlocal.1
      have haup : bbStep rule G p x j ≤ 2 / m := hlocal.2.1
      have hstepdiff : |bbStep rule G p x j - bbStep rule A p x j| ≤
          (8 * directionConstant m M / d) * (Ω * S ^ j) + secantConstant m M * Ω := by
        rw [quadratic_bbStep]
        calc
          _ ≤ |bbStep rule G p x j - frozenQuotient rule A
              (bbCurrent rule G p x j - bbPrevious rule G p x j)| +
            |frozenQuotient rule A (bbCurrent rule G p x j - bbPrevious rule G p x j) -
              frozenQuotient rule A (bbCurrent rule A p x j - bbPrevious rule A p x j)| := abs_sub_le _ _ _
          _ ≤ secantConstant m M * Ω + (8 * directionConstant m M / d) * (Ω * S ^ j) :=
            add_le_add hlocal.2.2 hsep.2
          _ = _ := by ring
      have hactualCur : bbCurrent rule G p x j ≠ 0 := by
        have hn : ‖bbCurrent rule A p x j‖ - ‖bbCurrent rule G p x j‖ ≤
            ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ := by
          simpa only [norm_sub_rev] using norm_sub_norm_le (bbCurrent rule A p x j) (bbCurrent rule G p x j)
        have hδR := mul_le_mul_of_nonneg_right δtau hR.le
        have hlow := hpre j hjq'
        have hpositive : 0 < ‖bbCurrent rule G p x j‖ := by nlinarith only [hn, herr, hδR, hlow, mul_pos hτ hR]
        exact norm_pos_iff.mp hpositive
      have hGcur := h.local_map_ne_zero G _ Ω hactualCur hΩm hgradRem
      have hupdate := h.update_tracking_bound (bbCurrent rule G p x j) (bbCurrent rule A p x j)
        (G (bbCurrent rule G p x j)) (bbStep rule G p x j) (bbStep rule A p x j)
        (Ω * S ^ j) Ω ‖x‖ (D + 1) (8 * directionConstant m M / d)
        δnonneg hΩ hR.le hC.le ha0 hapos.le haup haHat haHatup herr hcurNorm hgradRem hstepdiff
      have hΩδ : Ω ≤ Ω * S ^ j := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_pow_of_one_le hS j) hΩ
      have hscalar :
          (1 + M / m + (8 * directionConstant m M / d) * M * (D + 1)) * (Ω * S ^ j) +
          (D + 1) * (M * secantConstant m M + 2 / m) * Ω ≤ S * (Ω * S ^ j) := by
        calc
          _ ≤ (1 + M / m + (8 * directionConstant m M / d) * M * (D + 1)) * (Ω * S ^ j) +
              (D + 1) * (M * secantConstant m M + 2 / m) * (Ω * S ^ j) :=
            add_le_add_left (mul_le_mul_of_nonneg_left hΩδ hB) _
          _ = ((1 + M / m + (8 * directionConstant m M / d) * M * (D + 1)) +
              (D + 1) * (M * secantConstant m M + 2 / m)) * (Ω * S ^ j) := by ring
          _ ≤ S * (Ω * S ^ j) := mul_le_mul_of_nonneg_right hSbound δnonneg
      have hnext : ‖bbCurrent rule G p x (j + 1) - bbCurrent rule A p x (j + 1)‖ ≤
          Ω * S ^ (j + 1) * ‖x‖ := by
        rw [bbCurrent_succ, bbCurrent_succ]
        apply hupdate.trans
        calc
          _ ≤ (S * (Ω * S ^ j)) * ‖x‖ := mul_le_mul_of_nonneg_right hscalar hR.le
          _ = _ := by rw [pow_succ]; ring
      refine ⟨?_, ?_⟩
      · intro i hi
        by_cases heq : i = j + 1
        · simpa only [heq] using hnext
        · exact old.1 i (by omega)
      · intro i hi
        by_cases heq : i = j
        · simpa only [heq] using And.intro hsep.1 (And.intro hGcur hapos)
        · exact old.2 i (by omega)
  have hall := induction_claim q le_rfl
  refine ⟨?_, hall.2⟩
  intro j hj
  refine ⟨hall.1 j hj, ?_⟩
  have hactual := actualNorm j (by omega) (hall.1 j hj)
  have hfrozen := frozenNorm j (by omega)
  nlinarith only [hactual, hfrozen]

/-- All arithmetic constants needed by finite tracking can be chosen uniformly. -/
theorem PositiveModel.tracking_constants (h : PositiveModel A m M) (N : ℕ) (τ : ℝ) (hτ : 0 < τ) :
    ∃ D S : ℝ, 1 ≤ D ∧ (1 + M / m) ^ N ≤ D ∧ 1 ≤ S ∧
      (1 + M / m + (8 * directionConstant m M / (m * τ / M)) * M * (D + 1)) +
        (D + 1) * (M * secantConstant m M + 2 / m) ≤ S := by
  have hm := h.m_pos
  have hM := h.M_pos
  have hsec := h.secantConstant_pos
  have hdir := h.directionConstant_pos
  let D := (1 + M / m) ^ N
  have hD : 1 ≤ D := one_le_pow_of_one_le (le_add_of_nonneg_right (div_nonneg hM.le hm.le) : 1 ≤ 1 + M / m) N
  let K := 1 + M / m + (8 * directionConstant m M / (m * τ / M)) * M * (D + 1)
  let B := (D + 1) * (M * secantConstant m M + 2 / m)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨D, 1 + K + B, hD, le_rfl, ?_, ?_⟩ <;> change _ ≤ 1 + K + B
  · linarith only [hK, hB]
  · change K + B ≤ 1 + K + B
    linarith

/-- Finite-horizon tracking in its uniform epsilon-delta form.

This proves actual trajectory comparison and every nonterminal quotient's
legitimacy.  The prescribed error tolerance can be arbitrarily small; the growth
constant depends only on the model and N, while the radius also uses the strict
derivative and the pre-hitting threshold.
-/
theorem PositiveModel.finite_horizon_tracking (h : PositiveModel A m M) (rule : Rule)
    (G : E → E) (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (N : ℕ) (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) :
    ∃ D ≥ 1, ∃ r > 0, ∀ p x : E, ‖p‖ ≤ r → ‖x‖ ≤ r → p ≠ x → x ≠ 0 →
      ∀ q ≤ N, (∀ j < q, τ * ‖x‖ ≤ ‖bbCurrent rule A p x j‖) →
      (∀ j ≤ q, ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ ≤ η * ‖x‖ ∧
        ‖bbCurrent rule G p x j‖ + ‖bbCurrent rule A p x j‖ ≤ D * ‖x‖) ∧
      (∀ j < q, bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
        G (bbCurrent rule G p x j) ≠ 0 ∧ 0 < bbStep rule G p x j) := by
  obtain ⟨D, S, hD, hDpow, hS, hSbound⟩ := h.tracking_constants N τ hτ
  have hm := h.m_pos
  have hM := h.M_pos
  have hC : 0 < D + 1 := by linarith
  have hSp : 0 < S ^ N := pow_pos (by linarith : 0 < S) N
  let d := m * τ / M
  have hd : 0 < d := by dsimp [d]; positivity
  let σ := min 1 (min (τ / 2) (d / 4))
  have _hσ : 0 < σ := by dsimp [σ]; positivity
  let Ω := min (m / 2) (min (σ / S ^ N) (η / S ^ N))
  have hΩp : 0 < Ω := by dsimp [Ω]; positivity
  have hΩhalf : Ω ≤ m / 2 := min_le_left _ _
  have hΩσ : Ω * S ^ N ≤ σ :=
    (le_div_iff hSp).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hΩη : Ω * S ^ N ≤ η :=
    (le_div_iff hSp).mp ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨b, hb, hball⟩ := strict_derivative_closed_ball_estimate G A 0 hstrict Ω hΩp
  let r := b / (D + 1)
  have hr : 0 < r := div_pos hb hC
  have hCr : (D + 1) * r = b := by dsimp [r]; field_simp
  have hrem : ∀ u, ‖u‖ ≤ (D + 1) * r → ∀ v, ‖v‖ ≤ (D + 1) * r →
      ‖G u - G v - A (u - v)‖ ≤ Ω * ‖u - v‖ := by
    intro u hu v hv
    apply hball u _ v _
    · simpa only [Metric.mem_closedBall, dist_zero_right, hCr] using hu
    · simpa only [Metric.mem_closedBall, dist_zero_right, hCr] using hv
  refine ⟨2 * D + 1, by linarith, r, hr, ?_⟩
  intro p x hp hx hpx hx0 q hq hpre
  have hex := h.finite_tracking_explicit rule G p x N q τ r Ω D S d hτ hr hΩp.le hΩhalf
    hD hDpow hS hd rfl hSbound hΩσ hG hrem hp hx hpx hx0 hq hpre
  refine ⟨?_, hex.2⟩
  intro j hj
  refine ⟨?_, (hex.1 j hj).2⟩
  apply (hex.1 j hj).1.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right hS (by omega : j ≤ N)) hΩp.le).trans hΩη

end BB.Nonlinear
