import Mathlib.Analysis.NormedSpace.WeakDual
import Mathlib.Topology.ContinuousFunction.Compact
import Mathlib.Analysis.NormedSpace.OperatorNorm.Mul
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.Tactic

/-!
# Compact positive normalized functionals

This constructs the compact scalar state space needed for a measure-free
Hilbert-space argument.  Compactness is proved by Banach--Alaoglu and closed
positivity/unitality conditions.  It is not assumed and does not rely on an
unavailable probability-measure compactness theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped Topology

namespace BB

variable {K : Type*} [TopologicalSpace K] [CompactSpace K]

def IsPositiveUnit (L : WeakDual ℝ C(K, ℝ)) : Prop :=
  (∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f) ∧ L 1 = 1

abbrev PositiveState (K : Type*) [TopologicalSpace K] [CompactSpace K] :=
  {L : WeakDual ℝ C(K, ℝ) // IsPositiveUnit L}

theorem positive_unit_mono {L : WeakDual ℝ C(K, ℝ)} (hL : IsPositiveUnit L)
    {f g : C(K, ℝ)} (hfg : ∀ x, f x ≤ g x) : L f ≤ L g := by
  have h := hL.1 (g - f) (fun x => sub_nonneg.mpr (hfg x))
  rw [map_sub] at h
  linarith

theorem positive_unit_const {L : WeakDual ℝ C(K, ℝ)} (hL : IsPositiveUnit L) (c : ℝ) :
    L (ContinuousMap.const K c) = c := by
  have heq : ContinuousMap.const K c = c • (1 : C(K, ℝ)) := by
    ext _
    simp
  rw [heq, _root_.map_smul, hL.2, smul_eq_mul, mul_one]

theorem positive_unit_abs_le_norm {L : WeakDual ℝ C(K, ℝ)} (hL : IsPositiveUnit L)
    (f : C(K, ℝ)) : |L f| ≤ ‖f‖ := by
  apply abs_le.mpr
  constructor
  · have h := positive_unit_mono hL (f := ContinuousMap.const K (-‖f‖))
      (g := f) (fun x => f.neg_norm_le_apply x)
    simpa only [positive_unit_const hL] using h
  · have h := positive_unit_mono hL (f := f)
      (g := ContinuousMap.const K ‖f‖) (fun x => f.apply_le_norm x)
    simpa only [positive_unit_const hL] using h

theorem positive_unit_norm_le_one {L : WeakDual ℝ C(K, ℝ)} (hL : IsPositiveUnit L) :
    ‖WeakDual.toNormedDual L‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro f
  simpa only [Real.norm_eq_abs, one_mul] using positive_unit_abs_le_norm hL f

theorem isPositiveUnit_isClosed : IsClosed {L : WeakDual ℝ C(K, ℝ) | IsPositiveUnit L} := by
  have hpos : IsClosed {L : WeakDual ℝ C(K, ℝ) |
      ∀ f : C(K, ℝ), (∀ x, 0 ≤ f x) → 0 ≤ L f} := by
    simp only [setOf_forall]
    apply isClosed_iInter
    intro f
    apply isClosed_iInter
    intro _
    exact isClosed_le continuous_const (WeakDual.eval_continuous f)
  exact hpos.inter (isClosed_eq (WeakDual.eval_continuous (1 : C(K, ℝ))) continuous_const)

theorem positiveState_isCompact : IsCompact {L : WeakDual ℝ C(K, ℝ) | IsPositiveUnit L} := by
  apply (WeakDual.isCompact_closedBall ℝ (0 : NormedSpace.Dual ℝ C(K, ℝ)) 1).of_isClosed_subset
    isPositiveUnit_isClosed
  intro L hL
  change WeakDual.toNormedDual L ∈ Metric.closedBall 0 1
  simpa only [Metric.mem_closedBall, dist_zero_right] using positive_unit_norm_le_one hL

instance positiveStateCompactSpace : CompactSpace (PositiveState K) :=
  isCompact_iff_compactSpace.mp positiveState_isCompact

def evaluationState (x : K) : PositiveState K :=
  ⟨NormedSpace.Dual.toWeakDual (ContinuousMap.evalCLM ℝ x),
    (fun f hf => hf x), by rfl⟩

instance [Nonempty K] : Nonempty (PositiveState K) :=
  ⟨evaluationState (Classical.choice ‹Nonempty K›)⟩

theorem positive_state_eval_continuous (f : C(K, ℝ)) :
    Continuous (fun L : PositiveState K => L.1 f) :=
  (WeakDual.eval_continuous f).comp continuous_subtype_val

theorem evaluationState_continuous : Continuous (evaluationState : K → PositiveState K) := by
  apply Continuous.subtype_mk
  apply WeakDual.continuous_of_continuous_eval
  intro f
  exact f.continuous

/-- Multiplication by a nonnegative density followed by normalization. -/
def positiveReweight (L : PositiveState K) (q : C(K, ℝ))
    (hq : ∀ x, 0 ≤ q x) (hLq : 0 < L.1 q) : PositiveState K :=
  ⟨NormedSpace.Dual.toWeakDual ((L.1 q)⁻¹ •
      (WeakDual.toNormedDual L.1).comp (ContinuousLinearMap.mul ℝ C(K, ℝ) q)),
    (by
      intro f hf
      change 0 ≤ (L.1 q)⁻¹ * L.1 (q * f)
      exact mul_nonneg (inv_nonneg.mpr hLq.le)
        (L.2.1 (q * f) (fun x => mul_nonneg (hq x) (hf x)))),
    (by
      change (L.1 q)⁻¹ * L.1 (q * 1) = 1
      rw [mul_one, inv_mul_cancel (ne_of_gt hLq)])⟩

theorem positiveReweight_apply (L : PositiveState K) (q : C(K, ℝ))
    (hq : ∀ x, 0 ≤ q x) (hLq : 0 < L.1 q) (f : C(K, ℝ)) :
    (positiveReweight L q hq hLq).1 f = L.1 (q * f) / L.1 q := by
  change (L.1 q)⁻¹ * L.1 (q * f) = L.1 (q * f) / L.1 q
  ring

/-- A zero nonnegative test mass remains zero under bounded nonnegative
reweighting. This is the continuous-band replacement for null-set persistence. -/
theorem positive_reweight_zero_test (L : PositiveState K) (q f : C(K, ℝ))
    (hq : ∀ x, 0 ≤ q x) (hLq : 0 < L.1 q)
    (hf : ∀ x, 0 ≤ f x) (hLf : L.1 f = 0) :
    (positiveReweight L q hq hLq).1 f = 0 := by
  have hnonneg : 0 ≤ L.1 (q * f) :=
    L.2.1 (q * f) (fun x => mul_nonneg (hq x) (hf x))
  have hle : L.1 (q * f) ≤ L.1 (‖q‖ • f) :=
    positive_unit_mono L.2 (fun x => mul_le_mul_of_nonneg_right (q.apply_le_norm x) (hf x))
  rw [_root_.map_smul, hLf, smul_zero] at hle
  rw [positiveReweight_apply, le_antisymm hle hnonneg, zero_div]

/-- A nonnegative test of zero mass annihilates every continuous multiplier. -/
theorem positive_unit_zero_mul (L : PositiveState K) (q f : C(K, ℝ))
    (hf : ∀ x, 0 ≤ f x) (hLf : L.1 f = 0) : L.1 (q * f) = 0 := by
  have hle : L.1 (q * f) ≤ L.1 (‖q‖ • f) :=
    positive_unit_mono L.2 (fun x => mul_le_mul_of_nonneg_right (q.apply_le_norm x) (hf x))
  have hge : L.1 ((-‖q‖) • f) ≤ L.1 (q * f) :=
    positive_unit_mono L.2 (fun x => mul_le_mul_of_nonneg_right (q.neg_norm_le_apply x) (hf x))
  rw [_root_.map_smul, hLf, smul_zero] at hle hge
  exact le_antisymm hle hge

theorem positive_unit_sum_one {ι : Type*} [Fintype ι]
    (L : PositiveState K) (φ : ι → C(K, ℝ)) (hsum : ∑ i, φ i = 1) :
    ∑ i, L.1 (φ i) = 1 := by
  rw [← map_sum, hsum]
  exact L.2.2

theorem positive_unit_lower_bound (L : PositiveState K) (f : C(K, ℝ)) (a : ℝ)
    (ha : ∀ x, a ≤ f x) : a ≤ L.1 f := by
  have h := positive_unit_mono L.2 (f := ContinuousMap.const K a) (g := f) ha
  simpa only [positive_unit_const L.2] using h

theorem positive_unit_upper_bound (L : PositiveState K) (f : C(K, ℝ)) (b : ℝ)
    (hb : ∀ x, f x ≤ b) : L.1 f ≤ b := by
  have h := positive_unit_mono L.2 (f := f) (g := ContinuousMap.const K b) hb
  simpa only [positive_unit_const L.2] using h

def quadraticMultiplier (lam : C(K, ℝ)) (u : ℝ) : C(K, ℝ) :=
  (1 - u⁻¹ • lam)^2

theorem quadraticMultiplier_apply (lam : C(K, ℝ)) (u : ℝ) (x : K) :
    quadraticMultiplier lam u x = (1 - lam x / u)^2 := by
  simp only [quadraticMultiplier, ContinuousMap.pow_apply, ContinuousMap.sub_apply,
    ContinuousMap.one_apply, ContinuousMap.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

theorem quadraticMultiplier_nonneg (lam : C(K, ℝ)) (u : ℝ) (x : K) :
    0 ≤ quadraticMultiplier lam u x := by
  rw [quadraticMultiplier_apply]
  exact sq_nonneg _

/-- The reweighted test integral depends on only three weakly continuous
moments. This avoids any unjustified joint continuity of weak-star evaluation. -/
theorem quadratic_test_identity (L : PositiveState K) (lam f : C(K, ℝ)) (u : ℝ) :
    L.1 (quadraticMultiplier lam u * f) =
      L.1 f - (2 * u⁻¹) * L.1 (lam * f) + (u⁻¹)^2 * L.1 (lam^2 * f) := by
  have heq : quadraticMultiplier lam u * f =
      f - (2 * u⁻¹) • (lam * f) + (u⁻¹)^2 • (lam^2 * f) := by
    ext x
    simp only [quadraticMultiplier, ContinuousMap.mul_apply, ContinuousMap.pow_apply,
      ContinuousMap.sub_apply, ContinuousMap.add_apply, ContinuousMap.one_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
    ring
  rw [heq, map_add, map_sub, _root_.map_smul, _root_.map_smul, smul_eq_mul, smul_eq_mul]

end BB
