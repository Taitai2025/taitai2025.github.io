import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.PSeries

/-!
# The logarithmic scalar orbit in the C² counterexample

This file formalizes the actual positive recurrence used in the manuscript,
including its critical root rate and the divergence of its critical rescaling.
The separate realization as a C² two-variable objective and the secant-interval
admissibility require further theorems; they are not assumptions hidden here.
-/

namespace BB.Counterexample

noncomputable section

open scoped BigOperators Topology
open Filter

/-- `h(r)=1/log(1/r)` on `0<r<1`, with its continuous value at zero. -/
def logModulus (r : ℝ) : ℝ := (-Real.log r)⁻¹

/-- The radius recurrence of the alternating two-coordinate trajectory. -/
def radius (c alpha r₀ : ℝ) : ℕ → ℝ
  | 0 => r₀
  | n + 1 => (c + alpha * logModulus (radius c alpha r₀ n)) * radius c alpha r₀ n

@[simp] theorem radius_zero (c alpha r₀ : ℝ) : radius c alpha r₀ 0 = r₀ := rfl

@[simp] theorem radius_succ (c alpha r₀ : ℝ) (n : ℕ) :
    radius c alpha r₀ (n + 1) =
      (c + alpha * logModulus (radius c alpha r₀ n)) * radius c alpha r₀ n := rfl

@[simp] theorem logModulus_zero : logModulus 0 = 0 := by simp [logModulus]

theorem logModulus_eq (r : ℝ) : logModulus r = 1 / Real.log (1 / r) := by
  simp [logModulus, one_div, Real.log_inv]

theorem logModulus_pos {r : ℝ} (hr : 0 < r) (hr₁ : r < 1) :
    0 < logModulus r := by
  exact inv_pos.mpr (neg_pos.mpr (Real.log_neg hr hr₁))

theorem logModulus_mono {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) (hs : s < 1) :
    logModulus r ≤ logModulus s := by
  simp only [logModulus, inv_eq_one_div]
  apply one_div_le_one_div_of_le (neg_pos.mpr (Real.log_neg (hr.trans_le hrs) hs))
  exact neg_le_neg (Real.log_le_log hr hrs)

/-- Positivity and invariance of the interval `(0,r₀]`. -/
theorem radius_invariant {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    ∀ n, 0 < radius c alpha r₀ n ∧ radius c alpha r₀ n ≤ r₀ := by
  intro n
  induction n with
  | zero => simp [hr₀]
  | succ n ih =>
    have hh := logModulus_pos ih.1 (ih.2.trans_lt hr₁)
    have hhm := logModulus_mono ih.1 ih.2 hr₁
    have hq : c + alpha * logModulus (radius c alpha r₀ n) ≤ gamma :=
      (add_le_add_left (mul_le_mul_of_nonneg_left hhm halpha) c).trans hsmall
    constructor
    · rw [radius_succ]
      exact mul_pos (by nlinarith) ih.1
    · rw [radius_succ]
      calc
        (c + alpha * logModulus (radius c alpha r₀ n)) * radius c alpha r₀ n
            ≤ gamma * radius c alpha r₀ n := mul_le_mul_of_nonneg_right hq ih.1.le
        _ ≤ radius c alpha r₀ n := by nlinarith [ih.1]
        _ ≤ r₀ := ih.2

/-- A positive geometric lower bound for every radius. -/
theorem radius_lower {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    ∀ n, c ^ n * r₀ ≤ radius c alpha r₀ n := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := logModulus_pos (hInv n).1 ((hInv n).2.trans_lt hr₁)
    rw [radius_succ, pow_succ]
    have hmul := mul_le_mul_of_nonneg_left ih hc.le
    nlinarith [(hInv n).1, mul_nonneg halpha hh.le]

/-- A geometric upper bound, with any chosen `gamma<1` satisfying smallness. -/
theorem radius_upper {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    ∀ n, radius c alpha r₀ n ≤ gamma ^ n * r₀ := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    have hh := logModulus_mono (hInv n).1 (hInv n).2 hr₁
    have hq : c + alpha * logModulus (radius c alpha r₀ n) ≤ gamma :=
      (add_le_add_left (mul_le_mul_of_nonneg_left hh halpha) c).trans hsmall
    calc
      radius c alpha r₀ (n + 1) ≤ gamma * radius c alpha r₀ n := by
        rw [radius_succ]
        exact mul_le_mul_of_nonneg_right hq (hInv n).1.le
      _ ≤ gamma * (gamma ^ n * r₀) := mul_le_mul_of_nonneg_left ih hgamma₀
      _ = gamma ^ (n + 1) * r₀ := by rw [pow_succ]; ring

/-- The radii converge to zero. -/
theorem radius_tendsto_zero {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (radius c alpha r₀) atTop (𝓝 0) := by
  apply squeeze_zero
    (fun n => (radius_invariant hc halpha hr₀ hr₁ hgamma hsmall n).1.le)
    (radius_upper hc halpha hr₀ hr₁ hgamma₀ hgamma hsmall)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hgamma₀ hgamma).mul_const r₀

/-- The logarithmic modulus tends to zero on the positive side. -/
theorem logModulus_tendsto_zero :
    Tendsto logModulus (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsWithin_zero_right)

/-- Logarithms turn the recurrence into an exact finite sum. -/
theorem radius_log_sum {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    ∀ n, Real.log (radius c alpha r₀ n) = Real.log r₀ +
      ∑ j in Finset.range n, Real.log (c + alpha * logModulus (radius c alpha r₀ j)) := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    rw [radius_succ, Real.log_mul, ih, Finset.sum_range_succ]
    · ring
    · have hh := logModulus_pos (hInv n).1 ((hInv n).2.trans_lt hr₁)
      exact ne_of_gt (by nlinarith)
    · exact ne_of_gt (hInv n).1

/-- The critical root factor is exactly `c`. -/
theorem radius_root_limit {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (fun n : ℕ => (radius c alpha r₀ n) ^ (1 / (n : ℝ))) atTop (𝓝 c) := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  have hrad := radius_tendsto_zero hc halpha hr₀ hr₁ hgamma₀ hgamma hsmall
  have hrad' : Tendsto (radius c alpha r₀) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hrad, eventually_of_forall (fun n => (hInv n).1)⟩
  have hh := logModulus_tendsto_zero.comp hrad'
  have hq : Tendsto (fun n => c + alpha * logModulus (radius c alpha r₀ n)) atTop (𝓝 c) := by
    simpa using tendsto_const_nhds.add (hh.const_mul alpha)
  have hlogq := (Real.continuousAt_log hc.ne').tendsto.comp hq
  have hcesaro := hlogq.cesaro
  have hconst : Tendsto (fun n : ℕ => Real.log r₀ / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlogs : Tendsto (fun n : ℕ => Real.log (radius c alpha r₀ n) / (n : ℝ))
      atTop (𝓝 (Real.log c)) := by
    convert hconst.add hcesaro using 1
    · ext n
      rw [radius_log_sum hc halpha hr₀ hr₁ hgamma hsmall n]
      simp only [Function.comp_apply]
      ring
    · simp
  have hexp := hlogs.rexp
  rw [Real.exp_log hc] at hexp
  convert hexp using 1
  ext n
  rw [Real.rpow_def_of_pos (hInv n).1]
  congr 1
  ring

/-- Rescaling by the claimed critical exponential factor. -/
def normalizedRadius (c alpha r₀ : ℝ) (n : ℕ) : ℝ :=
  radius c alpha r₀ n / (c ^ n * r₀)

/-- The normalized radius is at least one. -/
theorem one_le_normalizedRadius {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) (n : ℕ) :
    1 ≤ normalizedRadius c alpha r₀ n := by
  unfold normalizedRadius
  apply (le_div_iff (mul_pos (pow_pos hc n) hr₀)).mpr
  simpa using radius_lower hc halpha hr₀ hr₁ hgamma hsmall n

/-- Exact multiplicative recurrence for the normalized radius. -/
theorem normalizedRadius_succ {c alpha r₀ : ℝ} (hc : 0 < c) (hr₀ : 0 < r₀) (n : ℕ) :
    normalizedRadius c alpha r₀ (n + 1) =
      (1 + (alpha / c) * logModulus (radius c alpha r₀ n)) *
        normalizedRadius c alpha r₀ n := by
  unfold normalizedRadius
  rw [radius_succ, pow_succ]
  field_simp [hc.ne', hr₀.ne']
  ring_nf
  simp

/-- Products of positive increments dominate the sum of those increments.
This avoids an unnecessary smallness condition on `alpha*h/c`. -/
theorem normalizedRadius_sum_lower {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    ∀ n, 1 + (alpha / c) *
      (∑ j in Finset.range n, logModulus (radius c alpha r₀ j)) ≤
      normalizedRadius c alpha r₀ n := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  intro n
  induction n with
  | zero => simp [normalizedRadius, ne_of_gt hr₀]
  | succ n ih =>
    rw [Finset.sum_range_succ, normalizedRadius_succ hc hr₀ n]
    have hR := one_le_normalizedRadius hc halpha hr₀ hr₁ hgamma hsmall n
    have hterm := mul_nonneg (div_nonneg halpha hc.le)
      (logModulus_pos (hInv n).1 ((hInv n).2.trans_lt hr₁)).le
    nlinarith

/-- A harmonic lower bound for the actual modulus along the orbit. -/
theorem logModulus_radius_ge_harmonic {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 ≤ alpha)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) (n : ℕ) :
    (-Real.log r₀ - Real.log c)⁻¹ * (1 / ((n : ℝ) + 1)) ≤
      logModulus (radius c alpha r₀ n) := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  have hlower := radius_lower hc halpha hr₀ hr₁ hgamma hsmall n
  have hlog := Real.log_le_log (mul_pos (pow_pos hc n) hr₀) hlower
  rw [Real.log_mul (pow_pos hc n).ne' hr₀.ne', Real.log_pow] at hlog
  have hlogr := Real.log_neg hr₀ hr₁
  have hlogc := Real.log_neg hc hc₁
  have hden : 0 < -Real.log (radius c alpha r₀ n) :=
    neg_pos.mpr (Real.log_neg (hInv n).1 ((hInv n).2.trans_lt hr₁))
  have hbound : -Real.log (radius c alpha r₀ n) ≤
      (-Real.log r₀ - Real.log c) * ((n : ℝ) + 1) := by
    nlinarith
  calc
    (-Real.log r₀ - Real.log c)⁻¹ * (1 / ((n : ℝ) + 1)) =
        ((-Real.log r₀ - Real.log c) * ((n : ℝ) + 1))⁻¹ := by
      simp only [one_div, mul_inv_rev]
      ring
    _ ≤ (-Real.log (radius c alpha r₀ n))⁻¹ := inv_le_inv_of_le hden hbound
    _ = logModulus (radius c alpha r₀ n) := rfl

/-- The critical normalization grows at least as a harmonic partial sum. -/
theorem normalizedRadius_harmonic_lower {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 ≤ alpha)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) (n : ℕ) :
    1 + ((alpha / c) * (-Real.log r₀ - Real.log c)⁻¹) *
      (∑ j in Finset.range n, (1 / ((j : ℝ) + 1))) ≤
      normalizedRadius c alpha r₀ n := by
  have hsum : (-Real.log r₀ - Real.log c)⁻¹ *
      (∑ j in Finset.range n, (1 / ((j : ℝ) + 1))) ≤
      ∑ j in Finset.range n, logModulus (radius c alpha r₀ j) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ =>
      logModulus_radius_ge_harmonic hc hc₁ halpha hr₀ hr₁ hgamma hsmall j)
  have hmain := normalizedRadius_sum_lower hc halpha hr₀ hr₁ hgamma hsmall n
  have hscaled := mul_le_mul_of_nonneg_left hsum (div_nonneg halpha hc.le)
  nlinarith

/-- No fixed finite prefactor bounds this orbit by `c^n*r₀`. -/
theorem normalizedRadius_tendsto_atTop {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 < alpha)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (normalizedRadius c alpha r₀) atTop atTop := by
  have hC : 0 < (-Real.log r₀ - Real.log c) := by
    nlinarith [Real.log_neg hr₀ hr₁, Real.log_neg hc hc₁]
  have hcoef : 0 < (alpha / c) * (-Real.log r₀ - Real.log c)⁻¹ :=
    mul_pos (div_pos halpha hc) (inv_pos.mpr hC)
  have hscaled := Filter.Tendsto.const_mul_atTop hcoef
    Real.tendsto_sum_range_one_div_nat_succ_atTop
  have hbound := (tendsto_const_nhds (x := (1 : ℝ))).add_atTop hscaled
  exact tendsto_atTop_mono
    (normalizedRadius_harmonic_lower hc hc₁ halpha.le hr₀ hr₁ hgamma hsmall) hbound

/-- A direct quantified form of the failure of a critical prefactor. -/
theorem no_critical_prefactor {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 < alpha)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    ¬ ∃ K : ℝ, ∀ n, radius c alpha r₀ n ≤ K * c ^ n * r₀ := by
  rintro ⟨K, hK⟩
  have hlim := normalizedRadius_tendsto_atTop hc hc₁ halpha hr₀ hr₁ hgamma hsmall
  obtain ⟨n, hn⟩ := (hlim.eventually (eventually_ge_atTop (K + 1))).exists
  have hupper : normalizedRadius c alpha r₀ n ≤ K := by
    unfold normalizedRadius
    apply (div_le_iff (mul_pos (pow_pos hc n) hr₀)).mpr
    simpa [mul_assoc] using hK n
  linarith

/-- A concrete arbitrarily small starting radius satisfies the smallness bound. -/
theorem exists_small_radius {c alpha gamma delta : ℝ}
    (halpha : 0 ≤ alpha) (hcγ : c < gamma) (hdelta : 0 < delta) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < delta ∧ r₀ < 1 ∧
      c + alpha * logModulus r₀ ≤ gamma := by
  let L : ℝ := 1 + |Real.log delta| + alpha / (gamma - c)
  have hgc : 0 < gamma - c := sub_pos.mpr hcγ
  have hfrac : 0 ≤ alpha / (gamma - c) := div_nonneg halpha hgc.le
  have hL : 0 < L := by dsimp [L]; positivity
  have hlog : -L < Real.log delta := by
    dsimp [L]
    nlinarith [neg_le_abs (Real.log delta)]
  have hbound : alpha ≤ (gamma - c) * L := by
    have hcancel : (gamma - c) * (alpha / (gamma - c)) = alpha := by field_simp
    dsimp [L]
    nlinarith [mul_nonneg hgc.le (abs_nonneg (Real.log delta))]
  refine ⟨Real.exp (-L), Real.exp_pos _, ?_, ?_, ?_⟩
  · calc
      Real.exp (-L) < Real.exp (Real.log delta) := Real.exp_lt_exp.mpr hlog
      _ = delta := Real.exp_log hdelta
  · exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hL)
  · simp only [logModulus, Real.log_exp, neg_neg]
    have hdiv := (div_le_iff hL).mpr hbound
    simp only [div_eq_mul_inv] at hdiv
    linarith

/-- The actual logarithmic scalar recurrence gives arbitrarily small
counterexamples to a uniform critical prefactor. -/
theorem arbitrarily_small_scalar_counterexample {c alpha : ℝ}
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 < alpha) :
    ∀ delta : ℝ, 0 < delta → ∃ r₀ : ℝ,
      0 < r₀ ∧ r₀ < delta ∧ r₀ < 1 ∧
      Tendsto (fun n : ℕ => (radius c alpha r₀ n) ^ (1 / (n : ℝ))) atTop (𝓝 c) ∧
      Tendsto (normalizedRadius c alpha r₀) atTop atTop := by
  intro delta hdelta
  let gamma : ℝ := (c + 1) / 2
  have hcγ : c < gamma := by dsimp [gamma]; linarith
  have hγ₀ : 0 < gamma := hc.trans hcγ
  have hγ₁ : gamma < 1 := by dsimp [gamma]; linarith
  obtain ⟨r₀, hr₀, hrδ, hr₁, hsmall⟩ := exists_small_radius halpha.le hcγ hdelta
  exact ⟨r₀, hr₀, hrδ, hr₁,
    radius_root_limit hc halpha.le hr₀ hr₁ hγ₀.le hγ₁ hsmall,
    normalizedRadius_tendsto_atTop hc hc₁ halpha hr₀ hr₁ hγ₁ hsmall⟩


end

end BB.Counterexample
