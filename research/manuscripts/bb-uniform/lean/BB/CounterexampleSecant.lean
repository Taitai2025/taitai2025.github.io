import BB.CounterexampleSmooth
import BB.Sigma

/-!
# True secant admissibility of the explicit two-coordinate orbit

The secants below are formed from successive points and their genuine gradient
coordinates. They are not Rayleigh quotients of an assumed frozen Hessian.
-/

namespace BB.Counterexample

noncomputable section
open scoped Topology
open Filter Set

def dot2 (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

def normSq2 (x : ℝ × ℝ) : ℝ := dot2 x x

def secantBB1 (s y : ℝ × ℝ) : ℝ := normSq2 s / dot2 s y

def secantBB2 (s y : ℝ × ℝ) : ℝ := dot2 s y / normSq2 y

/-- Three strict dot-product gaps ensure that the actual constant step lies
strictly inside its true BB2--BB1 secant interval. -/
theorem secant_interval_of_dot_gaps {alpha : ℝ} (halpha : 0 < alpha)
    (g gp : ℝ × ℝ)
    (hP : 0 < dot2 g gp)
    (hE : dot2 g gp < normSq2 g)
    (hN : dot2 g gp < normSq2 gp) :
    let s : ℝ × ℝ := (-alpha * g.1, -alpha * g.2)
    let y : ℝ × ℝ := (gp.1 - g.1, gp.2 - g.2)
    0 < dot2 s y ∧ 0 < normSq2 y ∧
      secantBB2 s y < alpha ∧ alpha < secantBB1 s y := by
  dsimp only
  have hsy : dot2 (-alpha * g.1, -alpha * g.2) (gp.1 - g.1, gp.2 - g.2) =
      alpha * (normSq2 g - dot2 g gp) := by simp only [dot2, normSq2]; ring
  have hss : normSq2 (-alpha * g.1, -alpha * g.2) = alpha ^ 2 * normSq2 g := by
    simp only [normSq2, dot2]; ring
  have hyy : normSq2 (gp.1 - g.1, gp.2 - g.2) =
      normSq2 g + normSq2 gp - 2 * dot2 g gp := by simp only [normSq2, dot2]; ring
  have hsypos : 0 < dot2 (-alpha * g.1, -alpha * g.2) (gp.1 - g.1, gp.2 - g.2) := by
    rw [hsy]
    exact mul_pos halpha (sub_pos.mpr hE)
  have hyypos : 0 < normSq2 (gp.1 - g.1, gp.2 - g.2) := by rw [hyy]; linarith
  refine ⟨hsypos, hyypos, ?_, ?_⟩
  · unfold secantBB2
    apply (div_lt_iff hyypos).mpr
    rw [hsy, hyy]
    nlinarith [mul_pos halpha (sub_pos.mpr hN)]
  · unfold secantBB1
    apply (lt_div_iff hsypos).mpr
    rw [hsy, hss]
    nlinarith [mul_pos (sq_pos_of_pos halpha) hP]

/-- Gradient coordinates of the C² objective in the preceding module. -/
def coordinateGradient (a b sigma : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  ((a - logModulus z.1) * z.1, (b + logModulus (z.2 / sigma)) * z.2)

/-- The actual two-coordinate orbit. -/
def orbit (c alpha sigma r₀ : ℝ) (n : ℕ) : ℝ × ℝ :=
  (radius c alpha r₀ n, (-1 : ℝ) ^ n * sigma * radius c alpha r₀ n)

def previousNormalized (a b sigma r : ℝ) : ℝ × ℝ :=
  (a - logModulus r, sigma * (b + logModulus r))

def nextNormalized (a b sigma c alpha r : ℝ) : ℝ × ℝ :=
  ((c + alpha * logModulus r) * (a - logModulus ((c + alpha * logModulus r) * r)),
    -sigma * (c + alpha * logModulus r) *
      (b + logModulus ((c + alpha * logModulus r) * r)))

def scaledSigned (sign r : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (r * z.1, sign * r * z.2)

theorem logModulus_sign (r : ℝ) (n : ℕ) :
    logModulus ((-1 : ℝ) ^ n * r) = logModulus r := by
  by_cases hr : r = 0
  · simp [hr]
  · unfold logModulus
    rw [Real.log_mul (pow_ne_zero n (by norm_num)) hr, Real.log_pow]
    norm_num

/-- Exact normalized form of the gradient along the orbit. -/
theorem gradient_orbit_eq (a b c alpha r₀ : ℝ) {sigma : ℝ}
    (hsigma : sigma ≠ 0) (n : ℕ) :
    coordinateGradient a b sigma (orbit c alpha sigma r₀ n) =
      scaledSigned ((-1 : ℝ) ^ n) (radius c alpha r₀ n)
        (previousNormalized a b sigma (radius c alpha r₀ n)) := by
  have harg : ((-1 : ℝ) ^ n * sigma * radius c alpha r₀ n) / sigma =
      (-1 : ℝ) ^ n * radius c alpha r₀ n := by field_simp; ring
  ext <;> simp only [coordinateGradient, orbit, scaledSigned, previousNormalized]
  · ring
  · rw [harg, logModulus_sign]
    ring

/-- Exact normalized form of the next gradient. -/
theorem gradient_orbit_next_eq (a b c alpha r₀ : ℝ) {sigma : ℝ}
    (hsigma : sigma ≠ 0) (n : ℕ) :
    coordinateGradient a b sigma (orbit c alpha sigma r₀ (n + 1)) =
      scaledSigned ((-1 : ℝ) ^ n) (radius c alpha r₀ n)
        (nextNormalized a b sigma c alpha (radius c alpha r₀ n)) := by
  rw [gradient_orbit_eq a b c alpha r₀ hsigma (n + 1)]
  ext <;> simp only [scaledSigned, previousNormalized, nextNormalized, radius_succ, pow_succ]
  · ring
  · ring

/-- The point sequence is an actual constant-step gradient iteration. -/
theorem orbit_step (a b c alpha r₀ : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 0)
    (ha : 1 - alpha * a = c) (hb : 1 - alpha * b = -c) (n : ℕ) :
    orbit c alpha sigma r₀ (n + 1) =
      ( (orbit c alpha sigma r₀ n).1 - alpha *
          (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)).1,
        (orbit c alpha sigma r₀ n).2 - alpha *
          (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)).2 ) := by
  rw [gradient_orbit_eq a b c alpha r₀ hsigma n]
  ext <;> simp only [orbit, scaledSigned, previousNormalized, radius_succ, pow_succ]
  · linear_combination -(radius c alpha r₀ n) * ha
  · linear_combination -((-1 : ℝ) ^ n * sigma * radius c alpha r₀ n) * hb

theorem dot2_scaledSigned {sign : ℝ} (hsign : sign ^ 2 = 1)
    (r : ℝ) (x y : ℝ × ℝ) :
    dot2 (scaledSigned sign r x) (scaledSigned sign r y) = r ^ 2 * dot2 x y := by
  simp only [dot2, scaledSigned]
  calc
    r * x.1 * (r * y.1) + sign * r * x.2 * (sign * r * y.2) =
        r ^ 2 * (x.1 * y.1 + sign ^ 2 * x.2 * y.2) := by ring
    _ = r ^ 2 * (x.1 * y.1 + x.2 * y.2) := by rw [hsign]; ring

/-- The normalized current gradient depends continuously on radius at zero. -/
theorem previousNormalized_continuousAt (a b sigma : ℝ) :
    ContinuousAt (previousNormalized a b sigma) 0 := by
  exact (continuousAt_const.sub logModulus_continuousAt_zero).prod
    (continuousAt_const.mul (continuousAt_const.add logModulus_continuousAt_zero))

/-- The normalized next gradient also has a continuous value at zero. -/
theorem nextNormalized_continuousAt (a b sigma c alpha : ℝ) :
    ContinuousAt (nextNormalized a b sigma c alpha) 0 := by
  have hq : ContinuousAt (fun r => c + alpha * logModulus r) 0 :=
    continuousAt_const.add (continuousAt_const.mul logModulus_continuousAt_zero)
  have hqr : ContinuousAt (fun r => (c + alpha * logModulus r) * r) 0 := hq.mul continuousAt_id
  have hh : ContinuousAt (fun r => logModulus ((c + alpha * logModulus r) * r)) 0 := by
    have hh0 : ContinuousAt logModulus ((c + alpha * logModulus 0) * 0) := by
      simpa using logModulus_continuousAt_zero
    exact ContinuousAt.comp (f := fun r => (c + alpha * logModulus r) * r) hh0 hqr
  exact (hq.mul (continuousAt_const.sub hh)).prod
    ((continuousAt_const.mul hq).mul (continuousAt_const.add hh))

/-- One fixed radius makes all three strict secant gaps hold. -/
theorem exists_uniform_secant_radius {a b sigma c alpha : ℝ}
    (ha : 0 < a) (hc : 0 < c) (hc₁ : c < 1)
    (hhigh : (sigma * b) ^ 2 < a ^ 2)
    (hlow : (1 - c) * a ^ 2 < (1 + c) * (sigma * b) ^ 2) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ r : ℝ, |r| < delta →
      0 < dot2 (previousNormalized a b sigma r) (nextNormalized a b sigma c alpha r) ∧
      dot2 (previousNormalized a b sigma r) (nextNormalized a b sigma c alpha r) <
        normSq2 (previousNormalized a b sigma r) ∧
      dot2 (previousNormalized a b sigma r) (nextNormalized a b sigma c alpha r) <
        normSq2 (nextNormalized a b sigma c alpha r) := by
  let G := previousNormalized a b sigma
  let H := nextNormalized a b sigma c alpha
  have hG : ContinuousAt G 0 := previousNormalized_continuousAt a b sigma
  have hH : ContinuousAt H 0 := nextNormalized_continuousAt a b sigma c alpha
  have hP : ContinuousAt (fun r => dot2 (G r) (H r)) 0 :=
    (hG.fst.mul hH.fst).add (hG.snd.mul hH.snd)
  have hE : ContinuousAt (fun r => normSq2 (G r)) 0 :=
    (hG.fst.mul hG.fst).add (hG.snd.mul hG.snd)
  have hN : ContinuousAt (fun r => normSq2 (H r)) 0 :=
    (hH.fst.mul hH.fst).add (hH.snd.mul hH.snd)
  have hP0 : 0 < dot2 (G 0) (H 0) := by
    simp only [G, H, previousNormalized, nextNormalized, logModulus_zero, mul_zero,
      add_zero, sub_zero, dot2]
    nlinarith [mul_pos hc (sub_pos.mpr hhigh)]
  have hE0 : 0 < normSq2 (G 0) - dot2 (G 0) (H 0) := by
    simp only [G, H, previousNormalized, nextNormalized, logModulus_zero, mul_zero,
      add_zero, sub_zero, dot2, normSq2]
    nlinarith [mul_pos (sub_pos.mpr hc₁) (sq_pos_of_pos ha),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + c) (sq_nonneg (sigma * b))]
  have hN0 : 0 < normSq2 (H 0) - dot2 (G 0) (H 0) := by
    simp only [G, H, previousNormalized, nextNormalized, logModulus_zero, mul_zero,
      add_zero, sub_zero, dot2, normSq2]
    nlinarith [mul_pos hc (sub_pos.mpr hlow)]
  have hevent : ∀ᶠ r in 𝓝 (0 : ℝ),
      0 < dot2 (G r) (H r) ∧
      dot2 (G r) (H r) < normSq2 (G r) ∧
      dot2 (G r) (H r) < normSq2 (H r) := by
    filter_upwards [hP.tendsto.eventually (lt_mem_nhds hP0),
      (hE.sub hP).tendsto.eventually (lt_mem_nhds hE0),
      (hN.sub hP).tendsto.eventually (lt_mem_nhds hN0)] with r hp he hn
    exact ⟨hp, by linarith, by linarith⟩
  obtain ⟨delta, hd, hball⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨delta, hd, ?_⟩
  intro r hr
  apply hball
  simpa [Real.dist_eq] using hr

/-- The coordinate field represents the actual Fréchet differential of f. -/
theorem objective_differential (a b : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 0)
    {z : ℝ × ℝ} (hz : z ∈ constructionDomain sigma) (w : ℝ × ℝ) :
    (fderiv ℝ (separableObjective a b sigma) z) w =
      dot2 (coordinateGradient a b sigma z) w := by
  have h1 := (scalarPotential_hasDerivAt a (-1) hz.1).hasFDerivAt.comp z hasFDerivAt_fst
  have hv := (((scalarPotential_hasDerivAt b 1 hz.2).comp z.2
    ((hasDerivAt_id z.2).div_const sigma)).const_mul (sigma^2))
  have h2 := hv.hasFDerivAt.comp z hasFDerivAt_snd
  have hF := h1.add h2
  change HasFDerivAt (separableObjective a b sigma) _ z at hF
  rw [hF.fderiv]
  simp [dot2, coordinateGradient, coordinateBump]
  field_simp
  <;> ring

/-- A diagonal continuous linear map on coordinate pairs. -/
def diagonalMap (a b : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (a • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (b • ContinuousLinearMap.snd ℝ ℝ ℝ)

/-- Exact derivative of the actual gradient field: the diagonal Hessian. -/
theorem coordinateGradient_hasFDerivAt (a b : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 0)
    {z : ℝ × ℝ} (hz : z ∈ constructionDomain sigma) :
    HasFDerivAt (coordinateGradient a b sigma)
      (diagonalMap (a - modulusDerivative z.1) (b + modulusDerivative (z.2/sigma))) z := by
  have h1 := (separableGradient_derivative_first a hz.1).hasFDerivAt.comp z hasFDerivAt_fst
  have h2 := (separableGradient_derivative_second b hsigma hz.2).hasFDerivAt.comp z hasFDerivAt_snd
  convert h1.prod h2 using 1
  ext w <;> simp [diagonalMap, smul_eq_mul]

@[simp] theorem coordinateGradient_zero (a b sigma : ℝ) :
    coordinateGradient a b sigma (0,0) = (0,0) := by
  simp [coordinateGradient]

/-- The Hessian at the minimizer has the prescribed two eigenvalues a,b. -/
theorem coordinateGradient_derivative_zero (a b : ℝ) {sigma : ℝ} (hsigma : sigma ≠ 0) :
    fderiv ℝ (coordinateGradient a b sigma) (0,0) = diagonalMap a b := by
  have hz : (0,0) ∈ constructionDomain sigma := by norm_num [constructionDomain]
  simpa using (coordinateGradient_hasFDerivAt a b hsigma hz).fderiv

/-- Secant displacement between actual successive iterates. -/
def pointSecant (c alpha sigma r₀ : ℝ) (n : ℕ) : ℝ × ℝ :=
  orbit c alpha sigma r₀ (n + 1) - orbit c alpha sigma r₀ n

/-- True gradient difference between actual successive iterates. -/
def gradientSecant (a b c alpha sigma r₀ : ℝ) (n : ℕ) : ℝ × ℝ :=
  coordinateGradient a b sigma (orbit c alpha sigma r₀ (n + 1)) -
    coordinateGradient a b sigma (orbit c alpha sigma r₀ n)

theorem orbit_secants_strict {a b c alpha sigma r₀ gamma : ℝ}
    (hc : 0 < c) (halpha : 0 < alpha) (hsigma : sigma ≠ 0)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma)
    (ha : 1 - alpha * a = c) (hb : 1 - alpha * b = -c)
    (hgaps : ∀ r : ℝ, 0 < r → r ≤ r₀ →
      0 < dot2 (previousNormalized a b sigma r) (nextNormalized a b sigma c alpha r) ∧
      dot2 (previousNormalized a b sigma r) (nextNormalized a b sigma c alpha r) <
        normSq2 (previousNormalized a b sigma r) ∧
      dot2 (previousNormalized a b sigma r) (nextNormalized a b sigma c alpha r) <
        normSq2 (nextNormalized a b sigma c alpha r)) (n : ℕ) :
    0 < dot2 (pointSecant c alpha sigma r₀ n) (gradientSecant a b c alpha sigma r₀ n) ∧
    0 < normSq2 (gradientSecant a b c alpha sigma r₀ n) ∧
    secantBB2 (pointSecant c alpha sigma r₀ n) (gradientSecant a b c alpha sigma r₀ n) < alpha ∧
    alpha < secantBB1 (pointSecant c alpha sigma r₀ n) (gradientSecant a b c alpha sigma r₀ n) := by
  have hInv := radius_invariant hc halpha.le hr₀ hr₁ hgamma hsmall n
  have hgap := hgaps (radius c alpha r₀ n) hInv.1 hInv.2
  have hsign : ((-1 : ℝ) ^ n)^2 = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    norm_num
  have hG := gradient_orbit_eq a b c alpha r₀ hsigma n
  have hH := gradient_orbit_next_eq a b c alpha r₀ hsigma n
  have hP : 0 < dot2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n))
      (coordinateGradient a b sigma (orbit c alpha sigma r₀ (n+1))) := by
    rw [hG, hH, dot2_scaledSigned hsign]
    exact mul_pos (sq_pos_of_pos hInv.1) hgap.1
  have hE : dot2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n))
      (coordinateGradient a b sigma (orbit c alpha sigma r₀ (n+1))) <
      normSq2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)) := by
    unfold normSq2
    rw [hG, hH, dot2_scaledSigned hsign, dot2_scaledSigned hsign]
    exact mul_lt_mul_of_pos_left hgap.2.1 (sq_pos_of_pos hInv.1)
  have hN : dot2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ n))
      (coordinateGradient a b sigma (orbit c alpha sigma r₀ (n+1))) <
      normSq2 (coordinateGradient a b sigma (orbit c alpha sigma r₀ (n+1))) := by
    unfold normSq2
    rw [hG, hH, dot2_scaledSigned hsign, dot2_scaledSigned hsign]
    exact mul_lt_mul_of_pos_left hgap.2.2 (sq_pos_of_pos hInv.1)
  have hs : pointSecant c alpha sigma r₀ n =
      (-alpha * (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)).1,
       -alpha * (coordinateGradient a b sigma (orbit c alpha sigma r₀ n)).2) := by
    unfold pointSecant
    rw [orbit_step a b c alpha r₀ hsigma ha hb n]
    ext <;> change _ - _ = _ <;> ring
  have hresult := secant_interval_of_dot_gaps halpha
    (coordinateGradient a b sigma (orbit c alpha sigma r₀ n))
    (coordinateGradient a b sigma (orbit c alpha sigma r₀ (n+1))) hP hE hN
  rw [hs]
  exact hresult

/-- Arbitrarily small admissible trajectories for the actual objective.
This theorem uses the original paper's exact midpoint step and exact sigma. -/
theorem arbitrarily_small_admissible_orbits {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∀ delta : ℝ, 0 < delta → ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ < delta ∧ r₀ < 1 ∧
      BB.endpointRate a b + (2/(a+b)) * logModulus r₀ ≤ (BB.endpointRate a b + 1)/2 ∧
      Tendsto (fun n : ℕ => (radius (BB.endpointRate a b) (2/(a+b)) r₀ n) ^
        (1 / (n : ℝ))) atTop (𝓝 (BB.endpointRate a b)) ∧
      Tendsto (normalizedRadius (BB.endpointRate a b) (2/(a+b)) r₀) atTop atTop ∧
      ∀ n : ℕ,
        0 < dot2 (pointSecant (BB.endpointRate a b) (2/(a+b)) (BB.counterexampleSigma a b) r₀ n)
          (gradientSecant a b (BB.endpointRate a b) (2/(a+b)) (BB.counterexampleSigma a b) r₀ n) ∧
        0 < normSq2 (gradientSecant a b (BB.endpointRate a b) (2/(a+b))
          (BB.counterexampleSigma a b) r₀ n) ∧
        secantBB2 (pointSecant (BB.endpointRate a b) (2/(a+b)) (BB.counterexampleSigma a b) r₀ n)
          (gradientSecant a b (BB.endpointRate a b) (2/(a+b)) (BB.counterexampleSigma a b) r₀ n)
          < 2/(a+b) ∧
        2/(a+b) < secantBB1
          (pointSecant (BB.endpointRate a b) (2/(a+b)) (BB.counterexampleSigma a b) r₀ n)
          (gradientSecant a b (BB.endpointRate a b) (2/(a+b)) (BB.counterexampleSigma a b) r₀ n) := by
  intro delta hdelta
  let c := BB.endpointRate a b
  let alpha : ℝ := 2 / (a+b)
  let sigma := BB.counterexampleSigma a b
  have hc : 0 < c := BB.endpointRate_pos ha hab
  have hc₁ : c < 1 := BB.endpointRate_lt_one ha hab
  have hbpos : 0 < b := ha.trans hab
  have habpos : 0 < a + b := add_pos ha hbpos
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  obtain ⟨hsigma, hhigh, hlow⟩ := BB.counterexampleSigma_conditions ha hab
  obtain ⟨d, hd, hgaps⟩ := exists_uniform_secant_radius
    (alpha := alpha) ha hc hc₁ hhigh hlow
  let gamma : ℝ := (c+1)/2
  have hcγ : c < gamma := by dsimp [gamma]; linarith
  have hγ₀ : 0 < gamma := hc.trans hcγ
  have hγ₁ : gamma < 1 := by dsimp [gamma]; linarith
  obtain ⟨r₀, hr₀, hrmin, hr₁, hsmall⟩ :=
    exists_small_radius halpha.le hcγ (lt_min hdelta hd)
  have hrd : r₀ < d := hrmin.trans_le (min_le_right _ _)
  have hrel₁ : 1 - alpha*a = c := by
    dsimp [alpha, c, BB.endpointRate]
    field_simp [habpos.ne', (add_pos hbpos ha).ne']
    <;> ring
  have hrel₂ : 1 - alpha*b = -c := by
    dsimp [alpha, c, BB.endpointRate]
    field_simp [habpos.ne', (add_pos hbpos ha).ne']
    <;> ring
  refine ⟨r₀, hr₀, hrmin.trans_le (min_le_left _ _), hr₁, hsmall,
    radius_root_limit hc halpha.le hr₀ hr₁ hγ₀.le hγ₁ hsmall,
    normalizedRadius_tendsto_atTop hc hc₁ halpha hr₀ hr₁ hγ₁ hsmall, ?_⟩
  intro n
  apply orbit_secants_strict hc halpha hsigma.ne' hr₀ hr₁ hγ₁ hsmall hrel₁ hrel₂ _ n
  intro r hr hrr
  apply hgaps r
  rw [abs_of_pos hr]
  exact hrr.trans_lt hrd

end
end BB.Counterexample
