import BB.SpectralLipschitz
import BB.Endpoint
import Mathlib.Topology.MetricSpace.PseudoMetric

set_option autoImplicit false

namespace BB.Baseline
open scoped BigOperators Topology
open Filter

variable {ι : Type*} [Fintype ι]

noncomputable def squaredMass (u : ι → ℝ) : ℝ := ∑ i, (u i)^2
noncomputable def normalizedEnergy (u : ι → ℝ) (i : ι) : ℝ := (u i)^2 / squaredMass u

theorem squaredMass_pos {u : ι → ℝ} (hu : u ≠ 0) : 0 < squaredMass u := by
  exact lt_of_lt_of_le (sq_pos_of_pos (norm_pos_iff.mpr hu)) (BB.Spectral.sum_sq_ge_norm_sq u)

theorem normalizedEnergy_nonneg (u : ι → ℝ) (i : ι) : 0 ≤ normalizedEnergy u i :=
  div_nonneg (sq_nonneg _) (Finset.sum_nonneg (fun j _ => sq_nonneg _))

theorem normalizedEnergy_sum {u : ι → ℝ} (hu : u ≠ 0) : ∑ i, normalizedEnergy u i = 1 := by
  unfold normalizedEnergy
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (squaredMass_pos hu))

noncomputable def tau (lam z : ι → ℝ) : ℝ := ∑ i, lam i*z i

/-- The normalized Rayleigh quotient lies in the spectral interval. -/
theorem tau_bounds {lam z : ι → ℝ} {a b : ℝ} (hz : ∀ i, 0 ≤ z i)
    (hsum : ∑ i, z i = 1) (ha : ∀ i, a ≤ lam i) (hb : ∀ i, lam i ≤ b) :
    a ≤ tau lam z ∧ tau lam z ≤ b := by
  constructor
  · calc
      a = ∑ i, a*z i := by rw [← Finset.mul_sum,hsum,mul_one]
      _ ≤ tau lam z := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (ha i) (hz i))
  · calc
      tau lam z ≤ ∑ i, b*z i := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hb i) (hz i))
      _ = b := by rw [← Finset.mul_sum,hsum,mul_one]

noncomputable def transfer (θ wa wb : ℝ) : ℝ := -(θ/2)*Real.log wa-((1-θ)/2)*Real.log wb

/-- The normalized transfer function exactly removes the radial factor. -/
theorem transfer_normalized {R x y : ℝ} (hR : 0 < R) (hx : 0 < x) (hy : 0 < y) (θ : ℝ) :
    transfer θ (x^2/R^2) (y^2/R^2) = Real.log R-θ*Real.log x-(1-θ)*Real.log y := by
  unfold transfer
  rw [Real.log_div (pow_ne_zero _ (ne_of_gt hx)) (pow_ne_zero _ (ne_of_gt hR)),
      Real.log_div (pow_ne_zero _ (ne_of_gt hy)) (pow_ne_zero _ (ne_of_gt hR)),
      Real.log_pow,Real.log_pow,Real.log_pow]
  ring

/-- Equation (5.5) of the original Lyapunov note, at positive endpoint components. -/
theorem denormalization {R x y : ℝ} (hR : 0 < R) (hx : 0 < x) (hy : 0 < y) (θ : ℝ) :
    R*Real.exp (-transfer θ (x^2/R^2) (y^2/R^2)) = BB.geometricProduct θ x y := by
  rw [transfer_normalized hR hx hy]
  unfold BB.geometricProduct
  rw [Real.rpow_def_of_pos hx,Real.rpow_def_of_pos hy,← Real.exp_add]
  calc
    R*Real.exp (-(Real.log R-θ*Real.log x-(1-θ)*Real.log y)) =
      Real.exp (Real.log R)*Real.exp (-(Real.log R-θ*Real.log x-(1-θ)*Real.log y)) := by rw [Real.exp_log hR]
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

/-- The logarithmic coboundary is the exact endpoint dissipation after normalization. -/
theorem coboundary_identity {R R' P P' c D : ℝ}
    (hR : 0 < R) (hR' : 0 < R') (hP : 0 < P) (hc : 0 < c)
    (hstep : P' = c*Real.exp (-D)*P) :
    Real.log (R'/R) = Real.log c-D + (Real.log R'-Real.log P') - (Real.log R-Real.log P) := by
  rw [hstep,Real.log_mul (mul_ne_zero (ne_of_gt hc) (ne_of_gt (Real.exp_pos _))) (ne_of_gt hP),
    Real.log_mul (ne_of_gt hc) (ne_of_gt (Real.exp_pos _)),Real.log_exp,
    Real.log_div (ne_of_gt hR') (ne_of_gt hR)]
  ring

section Terminal
variable {X : Type*}

/-- Terminally extended finite-step multiplier. A terminal state has factor zero,
so later values of a totalized normalized map do not affect the multiplier. -/
def terminalMultiplier (r : X → ℝ) (T : X → X) : ℕ → X → ℝ
  | 0, _ => 1
  | n+1, x => r x*terminalMultiplier r T n (T x)

@[simp] theorem terminalMultiplier_zero (r : X → ℝ) (T : X → X) (x : X) :
    terminalMultiplier r T 0 x = 1 := rfl

@[simp] theorem terminalMultiplier_succ (r : X → ℝ) (T : X → X) (n : ℕ) (x : X) :
    terminalMultiplier r T (n+1) x = r x*terminalMultiplier r T n (T x) := rfl

theorem terminalMultiplier_terminal {r : X → ℝ} (T : X → X) {x : X} (hx : r x = 0) (n : ℕ) :
    terminalMultiplier r T (n+1) x = 0 := by simp [terminalMultiplier,hx]

theorem terminalMultiplier_nonneg {r : X → ℝ} (hr : ∀ x, 0 ≤ r x) (T : X → X) (n : ℕ) (x : X) :
    0 ≤ terminalMultiplier r T n x := by
  induction n generalizing x with
  | zero => norm_num [terminalMultiplier]
  | succ n ih => exact mul_nonneg (hr x) (ih (T x))

theorem terminalMultiplier_bound {r : X → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hr0 : ∀ x, 0 ≤ r x) (hrB : ∀ x, r x ≤ B) (T : X → X) (n : ℕ) (x : X) :
    terminalMultiplier r T n x ≤ B^n := by
  induction n generalizing x with
  | zero => simp [terminalMultiplier]
  | succ n ih =>
    calc
      terminalMultiplier r T (n+1) x ≤ B*(B^n) :=
        mul_le_mul (hrB x) (ih (T x)) (terminalMultiplier_nonneg hr0 T n (T x)) hB
      _ = B^(n+1) := by rw [pow_succ]; ring

/-- The full continuity argument of Lemma 6.1, including terminal states.
The map is only required to be continuous where the one-step multiplier is positive. -/
theorem terminalMultiplier_continuous [TopologicalSpace X]
    {r : X → ℝ} {T : X → X} {B : ℝ} (hB : 0 ≤ B)
    (hr0 : ∀ x, 0 ≤ r x) (hrB : ∀ x, r x ≤ B) (hr : Continuous r)
    (hT : ∀ x, 0 < r x → ContinuousAt T x) (n : ℕ) :
    Continuous (terminalMultiplier r T n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih =>
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : r x = 0
    · have hconv : Tendsto (fun y => r y*B^n) (𝓝 x) (𝓝 0) := by
        have hh : ContinuousAt (fun y => r y*B^n) x := hr.continuousAt.mul continuousAt_const
        simpa only [hx,zero_mul] using hh.tendsto
      have hupper (y : X) : terminalMultiplier r T (n+1) y ≤ r y*B^n :=
        mul_le_mul_of_nonneg_left (terminalMultiplier_bound hB hr0 hrB T n (T y)) (hr0 y)
      have hh := squeeze_zero (terminalMultiplier_nonneg hr0 T (n+1)) hupper hconv
      simpa only [ContinuousAt,terminalMultiplier_succ,hx,zero_mul] using hh
    · have hxpos : 0 < r x := lt_of_le_of_ne (hr0 x) (Ne.symm hx)
      exact hr.continuousAt.mul (ih.continuousAt.comp (hT x hxpos))

/-- Exact multiplicative cocycle, valid for the terminal extension as well. -/
theorem terminalMultiplier_add (r : X → ℝ) (T : X → X) (n m : ℕ) (x : X) :
    terminalMultiplier r T (n+m) x = terminalMultiplier r T n x *
      terminalMultiplier r T m ((T^[n]) x) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_add,terminalMultiplier_succ,ih,terminalMultiplier_succ]
    rw [Function.iterate_succ_apply]
    ring

end Terminal
end BB.Baseline
