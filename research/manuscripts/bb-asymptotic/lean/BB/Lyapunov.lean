import BB.Spectral
import BB.Endpoint
import BB.Cocycle
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-!
# A continuous endpoint Lyapunov function on the closed simplex

Unlike the logarithmic endpoint potential, this function remains finite and
continuous at every boundary face. Zero endpoint weights, endpoint Rayleigh
quotients, and a zero squared growth multiplier are included explicitly.
-/

namespace BB

noncomputable section

variable {ι : Type*}

def endpointLyapunov (a b : ℝ) (lo hi : ι) (w : ι → ℝ) : ℝ :=
  w lo ^ leftWeight a b * w hi ^ rightWeight a b

lemma endpointLyapunov_nonneg {a b : ℝ} {lo hi : ι} {w : ι → ℝ}
    (hlo : 0 ≤ w lo) (hhi : 0 ≤ w hi) :
    0 ≤ endpointLyapunov a b lo hi w :=
  mul_nonneg (Real.rpow_nonneg hlo _) (Real.rpow_nonneg hhi _)

lemma endpointLyapunov_continuous {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (lo hi : ι) : Continuous (endpointLyapunov a b lo hi) := by
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  exact ((continuous_apply lo).rpow_const (fun _ => Or.inr hp.le)).mul
    ((continuous_apply hi).rpow_const (fun _ => Or.inr hq.le))

lemma endpointLyapunov_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (lo hi : ι) (w : ι → ℝ) (hlo : 0 ≤ w lo) (hhi : 0 ≤ w hi) :
    endpointLyapunov a b lo hi w = 0 ↔ w lo = 0 ∨ w hi = 0 := by
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  unfold endpointLyapunov
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hl | hr
    · exact Or.inl ((Real.rpow_eq_zero_iff_of_nonneg hlo).mp hl).1
    · exact Or.inr ((Real.rpow_eq_zero_iff_of_nonneg hhi).mp hr).1
  · intro h
    rcases h with hl | hr
    · rw [hl, Real.zero_rpow (ne_of_gt hp), zero_mul]
    · rw [hr, Real.zero_rpow (ne_of_gt hq), mul_zero]

lemma sq_rpow_eq_rpow_sq (x p : ℝ) (hx : 0 ≤ x) : (x ^ 2) ^ p = (x ^ p) ^ 2 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx, mul_comm,
    Real.rpow_mul hx, Real.rpow_natCast]

/-- Exact cancellation of the normalization denominator, including zero masses
and zero endpoint multipliers. The sole strict positivity is that of `R`. -/
lemma power_weight_update_identity (x y wa wb R p q : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hwa : 0 ≤ wa) (hwb : 0 ≤ wb)
    (hR : 0 < R) (hpq : p + q = 1) :
    R * ((x ^ 2 * wa / R) ^ p * (y ^ 2 * wb / R) ^ q) =
      (x ^ p * y ^ q) ^ 2 * (wa ^ p * wb ^ q) := by
  have hden : R ^ p * R ^ q = R := by rw [← Real.rpow_add hR, hpq, Real.rpow_one]
  rw [Real.div_rpow (mul_nonneg (sq_nonneg x) hwa) hR.le,
    Real.div_rpow (mul_nonneg (sq_nonneg y) hwb) hR.le,
    Real.mul_rpow (sq_nonneg x) hwa, Real.mul_rpow (sq_nonneg y) hwb,
    sq_rpow_eq_rpow_sq x p hx, sq_rpow_eq_rpow_sq y q hy,
    div_mul_div_comm, hden]
  field_simp
  ring

lemma endpointProduct_nonneg {a b u : ℝ} (ha : 0 < a) (hu : u ∈ Set.Icc a b) :
    0 ≤ endpointProduct a b u := by
  have hup : 0 < u := ha.trans_le hu.1
  exact mul_nonneg
    (Real.rpow_nonneg (div_nonneg (sub_nonneg.mpr hu.1) hup.le) _)
    (Real.rpow_nonneg (div_nonneg (sub_nonneg.mpr hu.2) hup.le) _)

variable [Fintype ι]

lemma spectral_lyapunov_identity_of_mean_bounds {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hw : IsSimplex w) (hmean : mean lam z ∈ Set.Icc a b)
    (hR : 0 < growthSq lam w z) :
    growthSq lam w z * endpointLyapunov a b lo hi (weightUpdate lam w z) =
      endpointProduct a b (mean lam z) ^ 2 * endpointLyapunov a b lo hi w := by
  have hua : a ≤ mean lam z := hmean.1
  have hub : mean lam z ≤ b := hmean.2
  have hu : 0 < mean lam z := ha.trans_le hua
  have hx : 0 ≤ (mean lam z - a) / mean lam z := div_nonneg (sub_nonneg.mpr hua) hu.le
  have hy : 0 ≤ (b - mean lam z) / mean lam z := div_nonneg (sub_nonneg.mpr hub) hu.le
  have hl : (1 - a / mean lam z) ^ 2 = ((mean lam z - a) / mean lam z) ^ 2 := by
    field_simp
  have hh : (1 - b / mean lam z) ^ 2 = ((b - mean lam z) / mean lam z) ^ 2 := by
    field_simp
    ring
  have hpq := endpoint_weights_sum (ne_of_gt (by linarith : 0 < a + b))
  unfold endpointLyapunov weightUpdate multiplier endpointProduct
  rw [hlo, hhi, hl, hh]
  exact power_weight_update_identity _ _ _ _ _ _ _ hx hy (hw.1 lo) (hw.1 hi) hR hpq

lemma spectral_lyapunov_identity {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hw : IsSimplex w) (hz : IsSimplex z)
    (hR : 0 < growthSq lam w z) :
    growthSq lam w z * endpointLyapunov a b lo hi (weightUpdate lam w z) =
      endpointProduct a b (mean lam z) ^ 2 * endpointLyapunov a b lo hi w :=
  spectral_lyapunov_identity_of_mean_bounds ha hab hlo hhi hw
    ⟨mean_lower hz (fun i => (hlam i).1), mean_upper hz (fun i => (hlam i).2)⟩ hR

/-- Closed-simplex one-step law with only local mean bounds; eigenvalues outside
the active face need not lie in the chosen endpoint interval. -/
lemma spectral_lyapunov_step_of_mean_bounds {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hw : IsSimplex w) (hmean : mean lam z ∈ Set.Icc a b) :
    growthSq lam w z * endpointLyapunov a b lo hi (weightUpdate lam w z) ≤
      rate a b ^ 2 * endpointLyapunov a b lo hi w := by
  have hV : 0 ≤ endpointLyapunov a b lo hi w := endpointLyapunov_nonneg (hw.1 lo) (hw.1 hi)
  rcases eq_or_lt_of_le (growth_sq_nonneg hw) with hR | hR
  · rw [← hR, zero_mul]
    exact mul_nonneg (sq_nonneg _) hV
  · rw [spectral_lyapunov_identity_of_mean_bounds ha hab hlo hhi hw hmean hR]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left (endpointProduct_nonneg ha hmean) (endpoint_product_le ha hab hmean) 2) hV

/-- Global closed-simplex one-step Lyapunov law. -/
lemma spectral_lyapunov_step {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hw : IsSimplex w) (hz : IsSimplex z) :
    growthSq lam w z * endpointLyapunov a b lo hi (weightUpdate lam w z) ≤
      rate a b ^ 2 * endpointLyapunov a b lo hi w :=
  spectral_lyapunov_step_of_mean_bounds ha hab hlo hhi hw
    ⟨mean_lower hz (fun i => (hlam i).1), mean_upper hz (fun i => (hlam i).2)⟩

/-- Iteration of a one-step quadratic Lyapunov certificate, valid through zero
multipliers for any chosen total terminal continuation. -/
lemma prefix_product_lyapunov {X : Type*} (r : X → ℝ) (T : X → X) (V : X → ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (hstep : ∀ x, r x ^ 2 * V (T x) ≤ θ * V x) :
    ∀ n x, prefixProduct r T n x ^ 2 * V (T^[n] x) ≤ θ ^ n * V x := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ n ih =>
    intro x
    rw [prefix_product_succ, Function.iterate_succ_apply]
    calc
      (r x * prefixProduct r T n (T x)) ^ 2 * V (T^[n] (T x)) =
          r x ^ 2 * (prefixProduct r T n (T x) ^ 2 * V (T^[n] (T x))) := by ring
      _ ≤ r x ^ 2 * (θ ^ n * V (T x)) :=
        mul_le_mul_of_nonneg_left (ih (T x)) (sq_nonneg (r x))
      _ = θ ^ n * (r x ^ 2 * V (T x)) := by ring
      _ ≤ θ ^ n * (θ * V x) := mul_le_mul_of_nonneg_left (hstep x) (pow_nonneg hθ n)
      _ = θ ^ (n + 1) * V x := by rw [pow_succ]; ring

end
end BB
