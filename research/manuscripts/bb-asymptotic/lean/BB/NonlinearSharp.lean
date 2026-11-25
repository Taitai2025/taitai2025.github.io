import BB.NonlinearMain
import BB.NonlinearAux
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Actual smooth nonquadratic sharpness trajectories -/

noncomputable section
namespace BB.Nonlinear

open scoped BigOperators Topology

abbrev Plane := EuclideanSpace ℝ (Fin 2)

def planePoint (u v : ℝ) : Plane := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![u, v]

@[simp] theorem planePoint_zero (u v : ℝ) : planePoint u v 0 = u := rfl
@[simp] theorem planePoint_one (u v : ℝ) : planePoint u v 1 = v := rfl

theorem planePoint_eta (z : Plane) : planePoint (z 0) (z 1) = z := by
  ext i
  fin_cases i <;> rfl

theorem plane_inner (z w : Plane) : inner (𝕜 := ℝ) z w = z 0 * w 0 + z 1 * w 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]
  rfl

theorem plane_norm_sq (z : Plane) : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, plane_inner]
  ring

def planeDiagonal (m M : ℝ) : Plane →L[ℝ] Plane :=
  LinearMap.toContinuousLinearMap
    ({ toFun := fun z => planePoint (m * z 0) (M * z 1)
       map_add' := by intro x y; ext i; fin_cases i <;> simp [planePoint, mul_add]
       map_smul' := by intro c x; ext i; fin_cases i <;> simp [planePoint, mul_left_comm] } :
      Plane →ₗ[ℝ] Plane)

@[simp] theorem planeDiagonal_apply (m M : ℝ) (z : Plane) :
    planeDiagonal m M z = planePoint (m * z 0) (M * z 1) := rfl

theorem planeDiagonal_symmetric (m M : ℝ) : (planeDiagonal m M).toLinearMap.IsSymmetric := by
  intro z w
  change inner (𝕜 := ℝ) (planeDiagonal m M z) w = inner (𝕜 := ℝ) z (planeDiagonal m M w)
  simp only [plane_inner, planeDiagonal_apply, planePoint_zero, planePoint_one]
  ring

theorem planeDiagonal_bounds (m M : ℝ) (hmM : m ≤ M) (z : Plane) :
    m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (planeDiagonal m M z) ∧
      inner (𝕜 := ℝ) z (planeDiagonal m M z) ≤ M * ‖z‖ ^ 2 := by
  simp only [plane_norm_sq, plane_inner, planeDiagonal_apply, planePoint_zero, planePoint_one]
  have h0 := mul_nonneg (sub_nonneg.mpr hmM) (sq_nonneg (z 0))
  have h1 := mul_nonneg (sub_nonneg.mpr hmM) (sq_nonneg (z 1))
  constructor <;> nlinarith only [h0, h1]

def planeObjective (m M η r : ℝ) (z : Plane) : ℝ := sharpObjective m M η r (z 0) (z 1)

def planeGradient (m M η r : ℝ) (z : Plane) : Plane :=
  planePoint
    (m * z 0 - 4 * η * r ^ 2 * z 0 * ((z 1) ^ 2 - r ^ 2 * (z 0) ^ 2))
    (M * z 1 + 4 * η * z 1 * ((z 1) ^ 2 - r ^ 2 * (z 0) ^ 2))

theorem planeObjective_smooth (m M η r : ℝ) : ContDiff ℝ ⊤ (planeObjective m M η r) := by
  have h0 : ContDiff ℝ ⊤ (fun z : Plane => z 0) := (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).contDiff
  have h1 : ContDiff ℝ ⊤ (fun z : Plane => z 1) := (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).contDiff
  exact ((contDiff_const.mul (h0.pow 2)).add (contDiff_const.mul (h1.pow 2))).div_const 2 |>.add
    (contDiff_const.mul (((h1.pow 2).sub (contDiff_const.mul (h0.pow 2))).pow 2))

theorem planeObjective_hasGradientAt (m M η r : ℝ) (z : Plane) :
    HasGradientAt (planeObjective m M η r) (planeGradient m M η r z) z := by
  have h0 : HasFDerivAt (fun w : Plane => w 0) (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : Plane => w 1) (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) z :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hD := (h1.mul h1).sub ((h0.mul h0).const_mul (r ^ 2))
  have hh := ((((h0.mul h0).const_mul m).add ((h1.mul h1).const_mul M)).const_mul (1 / 2 : ℝ)).add
    ((hD.mul hD).const_mul η)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hh using 1 <;> ext w
  · simp only [planeObjective, sharpObjective, quartic]
    ring
  · simp only [InnerProductSpace.toDual_apply, plane_inner, planeGradient, planePoint_zero, planePoint_one,
      ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      EuclideanSpace.proj_apply, smul_eq_mul]
    ring

theorem planeGradient_on_lines (m M η r : ℝ) (z : Plane)
    (hline : (z 1) ^ 2 = r ^ 2 * (z 0) ^ 2) :
    planeGradient m M η r z = planeDiagonal m M z := by
  simp only [planeGradient, planeDiagonal_apply, hline, sub_self, mul_zero, sub_zero, add_zero]

theorem planeObjective_unique_minimum (m M η r : ℝ) (hm : 0 < m) (hmM : m ≤ M) (hη : 0 ≤ η) :
    ∀ z : Plane, 0 ≤ planeObjective m M η r z ∧ (planeObjective m M η r z = 0 ↔ z = 0) := by
  intro z
  have hlo := sharpObjective_lower_bound m M η r (z 0) (z 1) hmM hη
  have heq := sharpObjective_eq_zero_iff m M η r (z 0) (z 1) hm hmM hη
  constructor
  · exact (mul_nonneg (div_nonneg hm.le (by norm_num)) (add_nonneg (sq_nonneg _) (sq_nonneg _))).trans hlo
  · rw [planeObjective, heq]
    constructor
    · rintro ⟨h0, h1⟩
      ext i
      fin_cases i <;> assumption
    · intro hz
      subst z
      exact ⟨rfl, rfl⟩

theorem planeObjective_nonquadratic (m M η r : ℝ) (hη : 0 < η) :
    ¬ ∃ a b c : ℝ, ∀ v : ℝ,
      planeObjective m M η r (planePoint 0 v) = a * v ^ 2 + b * v + c := by
  exact sharpObjective_nonquadratic m M η r hη

theorem planeGradient_zero (m M η r : ℝ) : planeGradient m M η r 0 = 0 := by
  ext i
  fin_cases i <;> simp [planeGradient, planePoint]

theorem planeGradient_strictDerivative (m M η r : ℝ) :
    HasStrictFDerivAt (planeGradient m M η r) (planeDiagonal m M) 0 := by
  have h0 : HasStrictFDerivAt (fun w : Plane => w 0) (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasStrictFDerivAt
  have h1 : HasStrictFDerivAt (fun w : Plane => w 1) (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) 0 :=
    (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasStrictFDerivAt
  have hD := (h1.mul h1).sub ((h0.mul h0).const_mul (r ^ 2))
  have hu := (h0.const_mul m).sub ((h0.const_mul (4 * η * r ^ 2)).mul hD)
  have hv := (h1.const_mul M).add ((h1.const_mul (4 * η)).mul hD)
  have hh := (hu.smul_const (planePoint 1 0)).add (hv.smul_const (planePoint 0 1))
  convert hh using 1
  · ext z i
    fin_cases i <;> simp [planeGradient, planePoint, pow_two]
  · ext z i
    fin_cases i <;> simp [planeDiagonal, planePoint]

theorem planeObjective_hessian (m M η r : ℝ) :
    fderiv ℝ (gradient (planeObjective m M η r)) 0 = planeDiagonal m M := by
  have hgrad : gradient (planeObjective m M η r) = planeGradient m M η r := by
    funext z
    exact (planeObjective_hasGradientAt m M η r z).gradient
  rw [hgrad]
  exact (planeGradient_strictDerivative m M η r).hasFDerivAt.fderiv

/-- Point zero is the previous seed; the actual current orbit starts at point one. -/
def sharpPoint (c r t : ℝ) (n : ℕ) : Plane := planePoint (t * c ^ n) (t * r * (-c) ^ n)

theorem neg_power_square (c : ℝ) (n : ℕ) : ((-c) ^ n) ^ 2 = (c ^ n) ^ 2 := by
  calc
    ((-c) ^ n) ^ 2 = ((-c) ^ 2) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = (c ^ 2) ^ n := by rw [neg_sq]
    _ = (c ^ n) ^ 2 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem sharpPoint_on_lines (c r t : ℝ) (n : ℕ) :
    (sharpPoint c r t n 1) ^ 2 = r ^ 2 * (sharpPoint c r t n 0) ^ 2 := by
  simp only [sharpPoint, planePoint_zero, planePoint_one, mul_pow]
  rw [neg_power_square]
  ring

theorem sharpPoint_nonzero (c r t : ℝ) (hc : c ≠ 0) (ht : t ≠ 0) (n : ℕ) :
    sharpPoint c r t n ≠ 0 := by
  intro hz
  have hzero := congrArg (fun z : Plane => z 0) hz
  exact (mul_ne_zero ht (pow_ne_zero _ hc)) hzero

theorem sharpPoint_norm (c r t : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    ‖sharpPoint c r t n‖ = c ^ n * ‖sharpPoint c r t 0‖ := by
  have hs : ‖sharpPoint c r t n‖ ^ 2 = (c ^ n * ‖sharpPoint c r t 0‖) ^ 2 := by
    simp only [mul_pow, plane_norm_sq, sharpPoint, planePoint_zero, planePoint_one,
      pow_zero, mul_one, neg_power_square]
    ring
  have hl := norm_nonneg (sharpPoint c r t n)
  have hr := mul_nonneg (pow_nonneg hc n) (norm_nonneg (sharpPoint c r t 0))
  nlinarith only [hs, hl, hr]

theorem sharpPoint_gradient_norm (m M η c r t : ℝ) (hc : 0 ≤ c) (n : ℕ) :
    ‖planeGradient m M η r (sharpPoint c r t n)‖ =
      c ^ n * ‖planeGradient m M η r (sharpPoint c r t 0)‖ := by
  rw [planeGradient_on_lines _ _ _ _ _ (sharpPoint_on_lines c r t n),
    planeGradient_on_lines _ _ _ _ _ (sharpPoint_on_lines c r t 0)]
  have hs : ‖planeDiagonal m M (sharpPoint c r t n)‖ ^ 2 =
      (c ^ n * ‖planeDiagonal m M (sharpPoint c r t 0)‖) ^ 2 := by
    simp only [mul_pow, plane_norm_sq, planeDiagonal_apply, sharpPoint,
      planePoint_zero, planePoint_one, pow_zero, mul_one, neg_power_square]
    ring
  have hl := norm_nonneg (planeDiagonal m M (sharpPoint c r t n))
  have hr := mul_nonneg (pow_nonneg hc n) (norm_nonneg (planeDiagonal m M (sharpPoint c r t 0)))
  nlinarith only [hs, hl, hr]

theorem sharpPoint_value (m M η c r t : ℝ) (n : ℕ) :
    planeObjective m M η r (sharpPoint c r t n) =
      c ^ (2 * n) * planeObjective m M η r (sharpPoint c r t 0) := by
  rw [planeObjective, planeObjective,
    (sharpObjective_matches_quadratic_on_lines m M η r _ _ (sharpPoint_on_lines c r t n)).1,
    (sharpObjective_matches_quadratic_on_lines m M η r _ _ (sharpPoint_on_lines c r t 0)).1]
  simp only [sharpPoint, planePoint_zero, planePoint_one, mul_pow, pow_zero, mul_one,
    neg_power_square, pow_mul]
  ring

theorem frozen_plane_long (m M : ℝ) (z : Plane) :
    frozenQuotient .long (planeDiagonal m M) z = diagonalBB1 m M (z 0) (z 1) := by
  simp only [frozenQuotient, Rule.quotient, bb1, plane_norm_sq, plane_inner,
    planeDiagonal_apply, planePoint_zero, planePoint_one, diagonalBB1]
  congr 1
  ring

theorem frozen_plane_short (m M : ℝ) (z : Plane) :
    frozenQuotient .short (planeDiagonal m M) z = diagonalBB2 m M (z 0) (z 1) := by
  simp only [frozenQuotient, Rule.quotient, bb2, plane_norm_sq, plane_inner,
    planeDiagonal_apply, planePoint_zero, planePoint_one, diagonalBB2]
  congr 1 <;> ring

theorem sharpPoint_update (m M r t : ℝ) (hden : m + M ≠ 0) (n : ℕ) :
    sharpPoint (rate m M) r t (n + 1) = sharpPoint (rate m M) r t n -
      (2 / (m + M)) • planeDiagonal m M (sharpPoint (rate m M) r t n) := by
  have hh := endpoint_update_multipliers m M hden
  have h0 := congrArg (fun y : ℝ => (t * (rate m M) ^ n) * y) hh.1
  have h1 := congrArg (fun y : ℝ => (t * r * (-(rate m M)) ^ n) * y) hh.2
  dsimp only at h0 h1
  rw [neg_div] at h1
  change (t * (rate m M) ^ n) * (1 - (2 / (m + M)) * m) =
    (t * (rate m M) ^ n) * (rate m M) at h0
  change (t * r * (-(rate m M)) ^ n) * (1 - (2 / (m + M)) * M) =
    (t * r * (-(rate m M)) ^ n) * (-(rate m M)) at h1
  ext i
  fin_cases i
  · change t * (rate m M) ^ (n + 1) = t * (rate m M) ^ n -
      (2 / (m + M)) * (m * (t * (rate m M) ^ n))
    rw [pow_succ]
    nlinarith only [h0]
  · change t * r * (-(rate m M)) ^ (n + 1) = t * r * (-(rate m M)) ^ n -
      (2 / (m + M)) * (M * (t * r * (-(rate m M)) ^ n))
    rw [pow_succ]
    nlinarith only [h1]

theorem sharpPoint_secant (m M r t : ℝ) (hden : m + M ≠ 0) (n : ℕ) :
    sharpPoint (rate m M) r t (n + 1) - sharpPoint (rate m M) r t n =
      -(2 / (m + M)) • planeDiagonal m M (sharpPoint (rate m M) r t n) := by
  rw [sharpPoint_update m M r t hden n, neg_smul]
  abel

theorem sharpPoint_balanced_quotient (rule : Rule) (m M c r t : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (ht : t ≠ 0)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) (n : ℕ) :
    frozenQuotient rule (planeDiagonal m M) (planeDiagonal m M (sharpPoint c r t n)) = 2 / (m + M) := by
  have hu : sharpPoint c r t n 0 ≠ 0 := mul_ne_zero ht (pow_ne_zero _ hc)
  have hb : m ^ rule.weightPower * (sharpPoint c r t n 0) ^ 2 =
      M ^ rule.weightPower * (sharpPoint c r t n 1) ^ 2 := by
    rw [sharpPoint_on_lines, hbalance]
    ring
  cases rule with
  | long =>
    rw [frozen_plane_long, planeDiagonal_apply, planePoint_zero, planePoint_one]
    apply balanced_diagonal_bb1 _ _ _ _ (mul_ne_zero hm hu)
    simpa only [Rule.weightPower, mul_pow] using hb
  | short =>
    rw [frozen_plane_short, planeDiagonal_apply, planePoint_zero, planePoint_one]
    apply balanced_diagonal_bb2 _ _ _ _ hm (mul_ne_zero hm hu)
    dsimp [Rule.weightPower] at hb
    nlinarith only [hb]

theorem sharpPoint_nonlinear_secant_step (rule : Rule) (m M η r t : ℝ)
    (hm : 0 < m) (hmM : m < M) (ht : t ≠ 0)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) (n : ℕ) :
    rule.quotient
      (sharpPoint (rate m M) r t (n + 1) - sharpPoint (rate m M) r t n)
      (planeGradient m M η r (sharpPoint (rate m M) r t (n + 1)) -
       planeGradient m M η r (sharpPoint (rate m M) r t n)) = 2 / (m + M) := by
  have hM : 0 < M := hm.trans hmM
  have hden : m + M ≠ 0 := (add_pos hm hM).ne'
  have hc : 0 < rate m M := div_pos (sub_pos.mpr hmM) (add_pos hM hm)
  rw [planeGradient_on_lines _ _ _ _ _ (sharpPoint_on_lines _ _ _ (n + 1)),
    planeGradient_on_lines _ _ _ _ _ (sharpPoint_on_lines _ _ _ n), ← map_sub]
  change frozenQuotient rule (planeDiagonal m M) _ = _
  rw [sharpPoint_secant m M r t hden n,
    frozenQuotient_smul rule _ _ _ (neg_ne_zero.mpr (div_ne_zero (by norm_num) hden))]
  exact sharpPoint_balanced_quotient rule m M (rate m M) r t hm.ne' hc.ne' ht hbalance n

/-- The recursively defined actual nonlinear state equals the explicit endpoint
orbit at every time; this includes the arbitrary incoming secant at time zero. -/
theorem sharpPoint_actual_state (rule : Rule) (m M η r t : ℝ)
    (hm : 0 < m) (hmM : m < M) (ht : t ≠ 0)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) :
    ∀ n, bbState rule (planeGradient m M η r)
      (sharpPoint (rate m M) r t 0) (sharpPoint (rate m M) r t 1) n =
      (sharpPoint (rate m M) r t n, sharpPoint (rate m M) r t (n + 1)) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bbState, bbTransition, ih]
    rw [sharpPoint_nonlinear_secant_step rule m M η r t hm hmM ht hbalance n,
      planeGradient_on_lines _ _ _ _ _ (sharpPoint_on_lines _ _ _ (n + 1)),
      ← sharpPoint_update m M r t (add_pos hm (hm.trans hmM)).ne' (n + 1)]

theorem sharpPoint_actual (rule : Rule) (m M η r t : ℝ)
    (hm : 0 < m) (hmM : m < M) (ht : t ≠ 0)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) (n : ℕ) :
    bbCurrent rule (planeGradient m M η r)
      (sharpPoint (rate m M) r t 0) (sharpPoint (rate m M) r t 1) n =
      sharpPoint (rate m M) r t (n + 1) :=
  congrArg Prod.snd (sharpPoint_actual_state rule m M η r t hm hmM ht hbalance n)

theorem sharpPoint_actual_steps (rule : Rule) (m M η r t : ℝ)
    (hm : 0 < m) (hmM : m < M) (ht : t ≠ 0)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) (n : ℕ) :
    bbStep rule (planeGradient m M η r)
      (sharpPoint (rate m M) r t 0) (sharpPoint (rate m M) r t 1) n = 2 / (m + M) := by
  simp only [bbStep, bbCurrent, bbPrevious,
    sharpPoint_actual_state rule m M η r t hm hmM ht hbalance]
  exact sharpPoint_nonlinear_secant_step rule m M η r t hm hmM ht hbalance n

theorem planeObjective_zero (m M η r : ℝ) : planeObjective m M η r 0 = 0 := by
  simp [planeObjective, sharpObjective, quartic]

/-- All three exact root factors belong to the actual nonlinear BB trajectory,
with any fixed positive normalization. -/
theorem nonquadratic_sharp_rootFactors (rule : Rule) (m M η r t R : ℝ)
    (hm : 0 < m) (hmM : m < M) (hη : 0 ≤ η) (ht : 0 < t) (hR : 0 < R)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) :
    let orbit := bbCurrent rule (planeGradient m M η r)
      (sharpPoint (rate m M) r t 0) (sharpPoint (rate m M) r t 1)
    rootFactor (fun n => ‖orbit n‖ / R) = rate m M ∧
      rootFactor (fun n => ‖planeGradient m M η r (orbit n)‖ / R) = rate m M ∧
      rootFactor (fun n => (planeObjective m M η r (orbit n) - planeObjective m M η r 0) / R ^ 2) =
        (rate m M) ^ 2 := by
  dsimp only
  let c := rate m M
  have hM : 0 < M := hm.trans hmM
  have hc : 0 < c := div_pos (sub_pos.mpr hmM) (add_pos hM hm)
  have hx : sharpPoint c r t 1 ≠ 0 := sharpPoint_nonzero c r t hc.ne' ht.ne' 1
  have hmodel := positiveModel_of_order_bounds (planeDiagonal m M) (planeDiagonal_symmetric m M)
    m M hm hmM.le (planeDiagonal_bounds m M hmM.le)
  have hg : planeGradient m M η r (sharpPoint c r t 1) ≠ 0 := by
    rw [planeGradient_on_lines _ _ _ _ _ (sharpPoint_on_lines c r t 1)]
    exact hmodel.map_ne_zero hx
  have hF : 0 < planeObjective m M η r (sharpPoint c r t 1) := by
    have hh := planeObjective_unique_minimum m M η r hm hmM.le hη (sharpPoint c r t 1)
    have hne : planeObjective m M η r (sharpPoint c r t 1) ≠ 0 := fun hz => hx (hh.2.mp hz)
    exact lt_of_le_of_ne hh.1 (Ne.symm hne)
  have heq : (fun n => ‖bbCurrent rule (planeGradient m M η r)
      (sharpPoint c r t 0) (sharpPoint c r t 1) n‖ / R) =
      fun n => (‖sharpPoint c r t 1‖ / R) * c ^ n := by
    funext n
    rw [sharpPoint_actual rule m M η r t hm hmM ht.ne' hbalance n,
      sharpPoint_norm c r t hc.le (n + 1), sharpPoint_norm c r t hc.le 1, pow_succ, pow_one]
    ring
  have hgeq : (fun n => ‖planeGradient m M η r (bbCurrent rule (planeGradient m M η r)
      (sharpPoint c r t 0) (sharpPoint c r t 1) n)‖ / R) =
      fun n => (‖planeGradient m M η r (sharpPoint c r t 1)‖ / R) * c ^ n := by
    funext n
    rw [sharpPoint_actual rule m M η r t hm hmM ht.ne' hbalance n,
      sharpPoint_gradient_norm m M η c r t hc.le (n + 1),
      sharpPoint_gradient_norm m M η c r t hc.le 1, pow_succ, pow_one]
    ring
  have hFeq : (fun n => (planeObjective m M η r (bbCurrent rule (planeGradient m M η r)
      (sharpPoint c r t 0) (sharpPoint c r t 1) n) - planeObjective m M η r 0) / R ^ 2) =
      fun n => (planeObjective m M η r (sharpPoint c r t 1) / R ^ 2) * (c ^ 2) ^ n := by
    funext n
    rw [sharpPoint_actual rule m M η r t hm hmM ht.ne' hbalance n, planeObjective_zero, sub_zero,
      sharpPoint_value m M η c r t (n + 1), sharpPoint_value m M η c r t 1]
    simp only [pow_mul, pow_succ, pow_one]
    ring
  rw [heq, hgeq, hFeq]
  exact ⟨rootFactor_geometric _ c (div_pos (norm_pos_iff.mpr hx) hR) hc.le,
    rootFactor_geometric _ c (div_pos (norm_pos_iff.mpr hg) hR) hc.le,
    rootFactor_geometric _ (c ^ 2) (div_pos hF (sq_pos_of_pos hR)) (sq_nonneg c)⟩

theorem sharpPoint_initial_distinct (m M r t : ℝ) (hm : 0 < m) (hmM : m < M) (ht : 0 < t) :
    sharpPoint (rate m M) r t 0 ≠ sharpPoint (rate m M) r t 1 := by
  have hc1 : rate m M < 1 :=
    (div_lt_one (add_pos (hm.trans hmM) hm)).mpr (by linarith only [hm])
  intro he
  have hh := congrArg (fun z : Plane => z 0) he
  change t * (rate m M) ^ 0 = t * (rate m M) ^ 1 at hh
  simp only [pow_zero, pow_one, mul_one] at hh
  have hprod := mul_pos ht (sub_pos.mpr hc1)
  nlinarith only [hh, hprod]

/-- The exact nonquadratic sharp trajectories start in every neighborhood of
the minimizer.  Their gradients never vanish and every BB step is positive. -/
theorem exists_small_nonquadratic_sharp_pair (rule : Rule) (m M η r ε : ℝ)
    (hm : 0 < m) (hmM : m < M) (hη : 0 ≤ η) (hε : 0 < ε)
    (hbalance : m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2) :
    ∃ p x : Plane, ‖p‖ ≤ ε ∧ ‖x‖ ≤ ε ∧ p ≠ x ∧
      (∀ n, bbCurrent rule (planeGradient m M η r) p x n ≠ 0 ∧
        0 < bbStep rule (planeGradient m M η r) p x n) ∧
      rootFactor (fun n => ‖bbCurrent rule (planeGradient m M η r) p x n‖ / max ‖p‖ ‖x‖) = rate m M ∧
      rootFactor (fun n => ‖planeGradient m M η r (bbCurrent rule (planeGradient m M η r) p x n)‖ /
        max ‖p‖ ‖x‖) = rate m M ∧
      rootFactor (fun n => (planeObjective m M η r (bbCurrent rule (planeGradient m M η r) p x n) -
        planeObjective m M η r 0) / (max ‖p‖ ‖x‖) ^ 2) = (rate m M) ^ 2 := by
  let c := rate m M
  let B := ‖sharpPoint c r 1 0‖
  let t := ε / (B + 1)
  have hB : 0 ≤ B := norm_nonneg _
  have hB1 : 0 < B + 1 := by linarith only [hB]
  have ht : 0 < t := div_pos hε hB1
  have hc : 0 < c := div_pos (sub_pos.mpr hmM) (add_pos (hm.trans hmM) hm)
  have hc1 : c < 1 :=
    (div_lt_one (add_pos (hm.trans hmM) hm)).mpr (by linarith only [hm])
  let p := sharpPoint c r t 0
  let x := sharpPoint c r t 1
  have hscale : p = t • sharpPoint c r 1 0 := by
    ext i
    fin_cases i <;> simp [p, sharpPoint, planePoint]
  have hp : ‖p‖ ≤ ε := by
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    change t * B ≤ ε
    have heq : t * (B + 1) = ε := by dsimp [t]; field_simp
    nlinarith only [heq, ht]
  have hx : ‖x‖ ≤ ε := by
    have heq : ‖x‖ = c * ‖p‖ := by
      simpa only [x, p, pow_one] using sharpPoint_norm c r t hc.le 1
    rw [heq]
    have hmul : c * ‖p‖ ≤ ‖p‖ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1.le (norm_nonneg p)
    exact hmul.trans hp
  have hpx : p ≠ x := sharpPoint_initial_distinct m M r t hm hmM ht
  have hroots := nonquadratic_sharp_rootFactors rule m M η r t (max ‖p‖ ‖x‖)
    hm hmM hη ht (initialRadius_pos p x hpx) hbalance
  refine ⟨p, x, hp, hx, hpx, ?_, hroots.1, hroots.2.1, hroots.2.2⟩
  intro n
  rw [sharpPoint_actual rule m M η r t hm hmM ht.ne' hbalance n,
    sharpPoint_actual_steps rule m M η r t hm hmM ht.ne' hbalance n]
  exact ⟨sharpPoint_nonzero c r t hc.ne' ht.ne' (n + 1),
    div_pos (by norm_num) (add_pos hm (hm.trans hmM))⟩

/-- A positive line ratio realizing exactly the required BB1 or BB2 balance. -/
theorem exists_sharp_line_ratio (rule : Rule) (m M : ℝ) (hm : 0 < m) (hM : 0 < M) :
    ∃ r > 0, m ^ rule.weightPower = M ^ rule.weightPower * r ^ 2 := by
  refine ⟨Real.sqrt (m ^ rule.weightPower / M ^ rule.weightPower),
    Real.sqrt_pos.mpr (div_pos (pow_pos hm _) (pow_pos hM _)), ?_⟩
  rw [Real.sq_sqrt (div_nonneg (pow_nonneg hm.le _) (pow_nonneg hM.le _))]
  field_simp

/-- The derivative has exactly the two prescribed spectral values. -/
theorem planeDiagonal_linear_spectrum (m M : ℝ) :
    spectrum ℝ (planeDiagonal m M).toLinearMap = {m, M} := by
  ext μ
  rw [← Module.End.hasEigenvalue_iff_mem_spectrum]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hμ
    obtain ⟨z, hz⟩ := hμ.exists_hasEigenvector
    have he := hz.apply_eq_smul
    by_cases h0 : z 0 = 0
    · have h1 : z 1 ≠ 0 := by
        intro hz1
        apply hz.2
        ext i
        fin_cases i <;> assumption
      have hh := congrArg (fun w : Plane => w 1) he
      change M * z 1 = μ * z 1 at hh
      have hprod : (M - μ) * z 1 = 0 := by nlinarith only [hh]
      exact Or.inr (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right h1)).symm
    · have hh := congrArg (fun w : Plane => w 0) he
      change m * z 0 = μ * z 0 at hh
      have hprod : (m - μ) * z 0 = 0 := by nlinarith only [hh]
      exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right h0)).symm
  · rintro (rfl | rfl)
    · apply Module.End.hasEigenvalue_of_hasEigenvector (x := planePoint 1 0)
      constructor
      · apply Module.End.mem_eigenspace_iff.mpr
        ext i
        fin_cases i <;> simp [planeDiagonal, planePoint]
      · intro hz
        have hh := congrArg (fun w : Plane => w 0) hz
        norm_num [planePoint] at hh
    · apply Module.End.hasEigenvalue_of_hasEigenvector (x := planePoint 0 1)
      constructor
      · apply Module.End.mem_eigenspace_iff.mpr
        ext i
        fin_cases i <;> simp [planeDiagonal, planePoint]
      · intro hz
        have hh := congrArg (fun w : Plane => w 1) hz
        norm_num [planePoint] at hh

def planeEndAlgebraEquiv : (Plane →L[ℝ] Plane) ≃ₐ[ℝ] (Plane →ₗ[ℝ] Plane) where
  toFun := ContinuousLinearMap.toLinearMap
  invFun := LinearMap.toContinuousLinearMap
  left_inv := by intro A; rfl
  right_inv := by intro A; rfl
  map_mul' := by intro A B; rfl
  map_add' := by intro A B; rfl
  commutes' := by intro a; rfl

theorem planeDiagonal_spectrum (m M : ℝ) : spectrum ℝ (planeDiagonal m M) = {m, M} := by
  rw [← AlgEquiv.spectrum_eq planeEndAlgebraEquiv (planeDiagonal m M)]
  exact planeDiagonal_linear_spectrum m M

theorem planeObjective_coercive (m M η r : ℝ) (hmM : m ≤ M) (hη : 0 ≤ η) (z : Plane) :
    (m / 2) * ‖z‖ ^ 2 ≤ planeObjective m M η r z := by
  simpa only [planeObjective, plane_norm_sq] using
    sharpObjective_lower_bound m M η r (z 0) (z 1) hmM hη

def HasSharpPair (rule : Rule) (F : Plane → ℝ) (G : Plane → Plane) (c ε : ℝ) : Prop :=
  ∃ p x : Plane, ‖p‖ ≤ ε ∧ ‖x‖ ≤ ε ∧ p ≠ x ∧
    (∀ n, bbCurrent rule G p x n ≠ 0 ∧ 0 < bbStep rule G p x n) ∧
    rootFactor (fun n => ‖bbCurrent rule G p x n‖ / max ‖p‖ ‖x‖) = c ∧
    rootFactor (fun n => ‖G (bbCurrent rule G p x n)‖ / max ‖p‖ ‖x‖) = c ∧
    rootFactor (fun n => (F (bbCurrent rule G p x n) - F 0) / (max ‖p‖ ‖x‖) ^ 2) = c ^ 2

/-- The prescribed endpoint class contains a C∞ genuinely nonquadratic
objective with its exact Hessian spectrum, unique global minimizer, and exact
sharp actual BB trajectories starting in every neighborhood. -/
theorem nonquadratic_sharpness (rule : Rule) (m M η : ℝ)
    (hm : 0 < m) (hmM : m < M) (hη : 0 < η) :
    ∃ r > 0,
      ContDiff ℝ ⊤ (planeObjective m M η r) ∧
      (∀ z, HasGradientAt (planeObjective m M η r) (planeGradient m M η r z) z) ∧
      planeGradient m M η r 0 = 0 ∧
      HasStrictFDerivAt (planeGradient m M η r) (planeDiagonal m M) 0 ∧
      fderiv ℝ (gradient (planeObjective m M η r)) 0 = planeDiagonal m M ∧
      spectrum ℝ (planeDiagonal m M) = {m, M} ∧
      (∀ z, (m / 2) * ‖z‖ ^ 2 ≤ planeObjective m M η r z) ∧
      (∀ z, 0 ≤ planeObjective m M η r z ∧ (planeObjective m M η r z = 0 ↔ z = 0)) ∧
      (¬ ∃ a b c : ℝ, ∀ v : ℝ,
        planeObjective m M η r (planePoint 0 v) = a * v ^ 2 + b * v + c) ∧
      ∀ ε > 0, HasSharpPair rule (planeObjective m M η r) (planeGradient m M η r) (rate m M) ε := by
  obtain ⟨r, hr, hbalance⟩ := exists_sharp_line_ratio rule m M hm (hm.trans hmM)
  exact ⟨r, hr, planeObjective_smooth m M η r, planeObjective_hasGradientAt m M η r,
    planeGradient_zero m M η r, planeGradient_strictDerivative m M η r,
    planeObjective_hessian m M η r, planeDiagonal_spectrum m M,
    planeObjective_coercive m M η r hmM.le hη.le,
    planeObjective_unique_minimum m M η r hm hmM.le hη.le,
    planeObjective_nonquadratic m M η r hη,
    fun ε hε => exists_small_nonquadratic_sharp_pair rule m M η r ε hm hmM hη.le hε hbalance⟩

end BB.Nonlinear
