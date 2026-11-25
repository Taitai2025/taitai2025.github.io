import BB.CounterexampleSecant

/-!
# Euclidean norm conclusions of the explicit counterexample

`norm2` is the ordinary Euclidean norm, written explicitly on a coordinate pair.
This avoids confusing it with the default maximum norm on Lean's product type.
-/

namespace BB.Counterexample

noncomputable section
open scoped Topology
open Filter

def norm2 (z : ℝ × ℝ) : ℝ := Real.sqrt (normSq2 z)

theorem normSq2_nonneg (z : ℝ × ℝ) : 0 ≤ normSq2 z := by
  dsimp [normSq2, dot2]
  nlinarith [sq_nonneg z.1, sq_nonneg z.2]

theorem norm2_nonneg (z : ℝ × ℝ) : 0 ≤ norm2 z := Real.sqrt_nonneg _

theorem norm2_scaledSigned {sign r : ℝ} (hsign : sign ^ 2 = 1) (hr : 0 ≤ r)
    (z : ℝ × ℝ) : norm2 (scaledSigned sign r z) = r * norm2 z := by
  unfold norm2 normSq2
  rw [dot2_scaledSigned hsign, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs,
    abs_of_nonneg hr]

theorem norm2_orbit {c alpha sigma r₀ : ℝ} {n : ℕ} (hr : 0 ≤ radius c alpha r₀ n) :
    norm2 (orbit c alpha sigma r₀ n) = radius c alpha r₀ n * Real.sqrt (1 + sigma^2) := by
  have hs : ((-1 : ℝ)^n)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have heq : orbit c alpha sigma r₀ n =
      scaledSigned ((-1 : ℝ)^n) (radius c alpha r₀ n) (1,sigma) := by
    ext <;> dsimp [orbit, scaledSigned] <;> ring
  rw [heq, norm2_scaledSigned hs hr]
  congr 1
  simp only [norm2, normSq2, dot2]
  congr 1
  ring

theorem norm2_gradient_orbit (a b c alpha r₀ : ℝ) {sigma : ℝ}
    (hsigma : sigma ≠ 0) {n : ℕ} (hr : 0 ≤ radius c alpha r₀ n) :
    norm2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)) =
      radius c alpha r₀ n * norm2 (previousNormalized a b sigma (radius c alpha r₀ n)) := by
  rw [gradient_orbit_eq a b c alpha r₀ hsigma n]
  apply norm2_scaledSigned _ hr
  rw [← pow_mul, Nat.mul_comm, pow_mul]
  norm_num

/-- A factor converging to a positive finite number has root factor one. -/
theorem positive_factor_root_limit {f : ℕ → ℝ} {L : ℝ}
    (hL : 0 < L) (hf : Tendsto f atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => f n ^ (1 / (n : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  have hlog := (Real.continuousAt_log hL.ne').tendsto.comp hf
  have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hexp := (hlog.mul hinv).rexp
  simp only [mul_zero, Real.exp_zero] at hexp
  apply hexp.congr'
  filter_upwards [hf.eventually (lt_mem_nhds hL)] with n hn
  exact (Real.rpow_def_of_pos hn (1 / (n : ℝ))).symm

/-- Multiplying the radii by a fixed positive norm factor preserves the root rate. -/
theorem orbit_norm_root_limit {c alpha sigma r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (fun n : ℕ => norm2 (orbit c alpha sigma r₀ n) ^ (1 / (n : ℝ)))
      atTop (𝓝 c) := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  have hconst := positive_factor_root_limit
    (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg sigma] : 0 < 1 + sigma^2))
    (tendsto_const_nhds (x := Real.sqrt (1 + sigma^2)))
  have hlim := (radius_root_limit hc halpha hr₀ hr₁ hgamma₀ hgamma hsmall).mul hconst
  simp only [mul_one] at hlim
  convert hlim using 1
  ext n
  rw [norm2_orbit (hInv n).1.le,
    Real.mul_rpow (hInv n).1.le (Real.sqrt_nonneg _)]

theorem orbit_norm_normalized_diverges {c alpha sigma r₀ gamma : ℝ}
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 < alpha)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma : gamma < 1) (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (fun n : ℕ => norm2 (orbit c alpha sigma r₀ n) /
      (c^n * norm2 (orbit c alpha sigma r₀ 0))) atTop atTop := by
  have hInv := radius_invariant hc halpha.le hr₀ hr₁ hgamma hsmall
  have hC : 0 < Real.sqrt (1 + sigma^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg sigma])
  convert normalizedRadius_tendsto_atTop hc hc₁ halpha hr₀ hr₁ hgamma hsmall using 1
  ext n
  rw [norm2_orbit (hInv n).1.le, norm2_orbit (hInv 0).1.le, radius_zero]
  unfold normalizedRadius
  field_simp
  <;> ring

/-- The normalized gradient size has a strictly positive finite limit. -/
theorem gradient_factor_limit {a : ℝ} (ha : 0 < a) (b sigma : ℝ)
    {c alpha r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (fun n : ℕ => norm2 (previousNormalized a b sigma (radius c alpha r₀ n)))
      atTop (𝓝 (Real.sqrt (a^2 + (sigma*b)^2))) := by
  have hG := previousNormalized_continuousAt a b sigma
  have hN : ContinuousAt (fun r => normSq2 (previousNormalized a b sigma r)) 0 :=
    (hG.fst.mul hG.fst).add (hG.snd.mul hG.snd)
  have hroot : ContinuousAt (fun r => norm2 (previousNormalized a b sigma r)) 0 :=
    Real.continuous_sqrt.continuousAt.comp hN
  have hlim := hroot.tendsto.comp
    (radius_tendsto_zero hc halpha hr₀ hr₁ hgamma₀ hgamma hsmall)
  convert hlim using 1
  congr 1
  simp only [norm2, normSq2, dot2, previousNormalized, logModulus_zero, sub_zero, add_zero]
  congr 1
  ring

/-- The Euclidean gradient norm has the same exact root factor. -/
theorem gradient_norm_root_limit {a b c alpha sigma r₀ gamma : ℝ}
    (ha : 0 < a) (hsigma : sigma ≠ 0)
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) :
    Tendsto (fun n : ℕ => norm2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)) ^
      (1 / (n : ℝ))) atTop (𝓝 c) := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall
  have hGpos : 0 < Real.sqrt (a^2 + (sigma*b)^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_pos ha, sq_nonneg (sigma*b)])
  have hG := positive_factor_root_limit hGpos
    (gradient_factor_limit ha b sigma hc halpha hr₀ hr₁ hgamma₀ hgamma hsmall)
  have hlim := (radius_root_limit hc halpha hr₀ hr₁ hgamma₀ hgamma hsmall).mul hG
  simp only [mul_one] at hlim
  convert hlim using 1
  ext n
  rw [norm2_gradient_orbit a b c alpha r₀ hsigma (hInv n).1.le,
    Real.mul_rpow (hInv n).1.le (norm2_nonneg _)]

/-- The Euclidean gradient normalization diverges whenever the initial gradient
is nonzero, as is guaranteed for the admissible orbits of the secant theorem. -/
theorem gradient_norm_normalized_diverges {a b c alpha sigma r₀ gamma : ℝ}
    (ha : 0 < a) (hsigma : sigma ≠ 0)
    (hc : 0 < c) (hc₁ : c < 1) (halpha : 0 < alpha)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1)
    (hgamma₀ : 0 ≤ gamma) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma)
    (hG₀ : 0 < norm2 (previousNormalized a b sigma r₀)) :
    Tendsto (fun n : ℕ => norm2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)) /
      (c^n * norm2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ 0)))) atTop atTop := by
  have hInv := radius_invariant hc halpha.le hr₀ hr₁ hgamma hsmall
  have hGpos : 0 < Real.sqrt (a^2 + (sigma*b)^2) :=
    Real.sqrt_pos.mpr (by nlinarith [sq_pos_of_pos ha, sq_nonneg (sigma*b)])
  have hfac := (gradient_factor_limit ha b sigma hc halpha.le hr₀ hr₁ hgamma₀ hgamma hsmall).div_const
    (norm2 (previousNormalized a b sigma r₀))
  have hR := normalizedRadius_tendsto_atTop hc hc₁ halpha hr₀ hr₁ hgamma hsmall
  have hlim := hR.atTop_mul (div_pos hGpos hG₀) hfac
  convert hlim using 1
  ext n
  rw [norm2_gradient_orbit a b c alpha r₀ hsigma (hInv n).1.le,
    norm2_gradient_orbit a b c alpha r₀ hsigma (hInv 0).1.le, radius_zero]
  unfold normalizedRadius
  ring

end
end BB.Counterexample
