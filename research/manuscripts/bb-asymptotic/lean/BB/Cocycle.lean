import Mathlib.Topology.Algebra.Order.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Tactic

/-!
# Products through a possibly discontinuous terminal update

The product is defined at every state. If its first multiplier is zero,
every positive-length product is zero regardless of the chosen terminal map.
This makes the actual finite products continuous even when the normalized
state update is discontinuous at termination.
-/

namespace BB
noncomputable section
open Filter
open scoped Topology

variable {X : Type*}

def prefixProduct (r : X → ℝ) (T : X → X) : ℕ → X → ℝ
  | 0, _ => 1
  | n+1, x => r x * prefixProduct r T n (T x)

@[simp] theorem prefix_product_zero (r : X → ℝ) (T : X → X) (x : X) :
    prefixProduct r T 0 x = 1 := rfl

@[simp] theorem prefix_product_succ (r : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    prefixProduct r T (n+1) x = r x * prefixProduct r T n (T x) := rfl

theorem prefix_product_nonneg (r : X → ℝ) (T : X → X)
    (hr : ∀ x, 0 ≤ r x) (n : ℕ) (x : X) : 0 ≤ prefixProduct r T n x := by
  induction n generalizing x with
  | zero => exact zero_le_one
  | succ n ih => exact mul_nonneg (hr x) (ih (T x))

theorem prefix_product_bound (r : X → ℝ) (T : X → X) (M : ℝ)
    (hM : 0 ≤ M) (hr : ∀ x, 0 ≤ r x) (hbound : ∀ x, r x ≤ M)
    (n : ℕ) (x : X) : prefixProduct r T n x ≤ M^n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [prefix_product_succ, pow_succ']
    exact mul_le_mul (hbound x) (ih (T x)) (prefix_product_nonneg r T hr n (T x)) hM

theorem prefix_product_terminal (r : X → ℝ) (T : X → X)
    (x : X) (hx : r x = 0) (n : ℕ) : prefixProduct r T (n+1) x = 0 := by
  simp only [prefix_product_succ,hx,zero_mul]

theorem prefix_product_cocycle (r : X → ℝ) (T : X → X) (n m : ℕ) (x : X) :
    prefixProduct r T (n+m) x =
      prefixProduct r T n x * prefixProduct r T m (T^[n] x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add, prefix_product_succ, ih, prefix_product_succ,
      Function.iterate_succ_apply, mul_assoc]

/-- The terminally extended finite multiplier is continuous. -/
theorem prefix_product_continuous [TopologicalSpace X]
    (r : X → ℝ) (T : X → X) (M : ℝ)
    (hM : 0 ≤ M) (hr : ∀ x, 0 ≤ r x) (hbound : ∀ x, r x ≤ M)
    (hrcont : Continuous r)
    (hTcont : ∀ x, r x ≠ 0 → ContinuousAt T x) :
    ∀ n, Continuous (prefixProduct r T n) := by
  intro n
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : r x = 0
    · have hzero : prefixProduct r T (n+1) x = 0 := prefix_product_terminal r T x hx n
      change Tendsto (prefixProduct r T (n+1)) (𝓝 x) (𝓝 (prefixProduct r T (n+1) x))
      rw [hzero]
      have ht : Tendsto (fun y => r y * M^n) (𝓝 x) (𝓝 0) := by
        have ht' : Tendsto (fun y => r y * M^n) (𝓝 x) (𝓝 (r x*M^n)) :=
          hrcont.continuousAt.mul_const (M^n)
        simpa only [hx,zero_mul] using ht'
      apply squeeze_zero (prefix_product_nonneg r T hr (n+1)) _ ht
      intro y
      exact mul_le_mul_of_nonneg_left (prefix_product_bound r T M hM hr hbound n (T y)) (hr y)
    · exact hrcont.continuousAt.mul (ih.continuousAt.comp (hTcont x hx))

end
end BB
