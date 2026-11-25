import BB.Counterexample
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Analysis.Convex.Deriv

/-!
# Smooth primitive underlying the logarithmic counterexample

The potentially singular logarithmic modulus is multiplied by its coordinate
before integration. This file verifies the derivatives at the coordinate axes
as well as away from them. All regularity assertions are local to `(-1,1)`.
-/

namespace BB.Counterexample

noncomputable section

open scoped Topology BigOperators
open Filter Set MeasureTheory

/-- Continuous extension of the modulus from both sides of zero. -/
theorem logModulus_tendsto_punctured :
    Tendsto logModulus (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsWithin_zero)

theorem logModulus_continuousAt_zero : ContinuousAt logModulus 0 := by
  change Tendsto logModulus (𝓝 (0 : ℝ)) (𝓝 (logModulus 0))
  rw [logModulus_zero]
  have hp : Tendsto logModulus (pure (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using tendsto_pure_nhds logModulus (0 : ℝ)
  have hsup : Tendsto logModulus ((𝓝[≠] (0 : ℝ)) ⊔ pure 0) (𝓝 (0 : ℝ)) :=
    tendsto_sup.mpr ⟨logModulus_tendsto_punctured, hp⟩
  simpa only [nhdsWithin_compl_singleton_sup_pure] using hsup

theorem logModulus_hasDerivAt {x : ℝ} (hx : x ≠ 0) (hl : Real.log x ≠ 0) :
    HasDerivAt logModulus (logModulus x ^ 2 / x) x := by
  have h := ((Real.hasDerivAt_log hx).neg).inv (neg_ne_zero.mpr hl)
  convert h using 1
  simp only [logModulus]
  field_simp
  <;> ring

theorem logModulus_continuousAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ContinuousAt logModulus x := by
  by_cases hzero : x = 0
  · simpa [hzero] using logModulus_continuousAt_zero
  · apply (logModulus_hasDerivAt hzero _).continuousAt
    have hl : Real.log x < 0 := by
      rw [← Real.log_abs]
      exact Real.log_neg (abs_pos.mpr hzero) (abs_lt.mpr hx)
    exact hl.ne

theorem logModulus_continuousOn : ContinuousOn logModulus (Ioo (-1 : ℝ) 1) :=
  fun _ hx => (logModulus_continuousAt hx).continuousWithinAt

/-- The derivative of the nonlinear part of the gradient. -/
def modulusDerivative (x : ℝ) : ℝ := logModulus x + logModulus x ^ 2

/-- The nonlinear part of one scalar gradient coordinate. -/
def coordinateBump (x : ℝ) : ℝ := x * logModulus x

@[simp] theorem coordinateBump_zero : coordinateBump 0 = 0 := by simp [coordinateBump]
@[simp] theorem modulusDerivative_zero : modulusDerivative 0 = 0 := by simp [modulusDerivative]

theorem coordinateBump_hasDerivAt_zero : HasDerivAt coordinateBump 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  convert logModulus_tendsto_punctured using 1
  ext t
  simp only [coordinateBump, zero_add, zero_mul, sub_zero, smul_eq_mul]
  by_cases ht : t = 0
  · simp [ht]
  · field_simp

theorem coordinateBump_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt coordinateBump (modulusDerivative x) x := by
  by_cases hzero : x = 0
  · simpa [hzero] using coordinateBump_hasDerivAt_zero
  · have hl : Real.log x ≠ 0 := by
      have hneg : Real.log x < 0 := by
        rw [← Real.log_abs]
        exact Real.log_neg (abs_pos.mpr hzero) (abs_lt.mpr hx)
      exact hneg.ne
    convert (hasDerivAt_id x).mul (logModulus_hasDerivAt hzero hl) using 1
    simp only [modulusDerivative]
    field_simp
    <;> ring

theorem coordinateBump_continuousOn : ContinuousOn coordinateBump (Ioo (-1 : ℝ) 1) :=
  fun _ hx => (coordinateBump_hasDerivAt hx).continuousAt.continuousWithinAt

theorem modulusDerivative_continuousOn :
    ContinuousOn modulusDerivative (Ioo (-1 : ℝ) 1) := by
  exact logModulus_continuousOn.add (logModulus_continuousOn.pow 2)

/-- The gradient ingredient is continuously differentiable, including at zero. -/
theorem coordinateBump_contDiffOn : ContDiffOn ℝ 1 coordinateBump (Ioo (-1 : ℝ) 1) := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 0) isOpen_Ioo).mpr
  constructor
  · exact fun _ hx => (coordinateBump_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · apply contDiffOn_zero.mpr
    apply modulusDerivative_continuousOn.congr
    intro x hx
    exact (coordinateBump_hasDerivAt hx).deriv

/-- A primitive of the nonlinear gradient ingredient. -/
def bumpPrimitive (u : ℝ) : ℝ := ∫ t in (0 : ℝ)..u, coordinateBump t

/-- Fundamental theorem of calculus on the actual local domain. -/
theorem bumpPrimitive_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt bumpPrimitive (coordinateBump x) x := by
  apply intervalIntegral.integral_hasDerivAt_right
  · apply ContinuousOn.intervalIntegrable
    apply coordinateBump_continuousOn.mono
    intro y hy
    rcases mem_uIcc.mp hy with hy | hy
    · constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    · constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  · exact coordinateBump_continuousOn.stronglyMeasurableAtFilter isOpen_Ioo x hx
  · exact (coordinateBump_hasDerivAt hx).continuousAt

/-- The scalar primitive is C² across the origin. -/
theorem bumpPrimitive_contDiffOn : ContDiffOn ℝ 2 bumpPrimitive (Ioo (-1 : ℝ) 1) := by
  apply (contDiffOn_succ_iff_deriv_of_isOpen (n := 1) isOpen_Ioo).mpr
  constructor
  · exact fun _ hx => (bumpPrimitive_hasDerivAt hx).differentiableAt.differentiableWithinAt
  · apply coordinateBump_contDiffOn.congr
    intro x hx
    exact (bumpPrimitive_hasDerivAt hx).deriv

/-- A scalar quadratic plus a signed logarithmic perturbation. -/
def scalarPotential (a sign u : ℝ) : ℝ := (a / 2) * u ^ 2 + sign * bumpPrimitive u

theorem scalarPotential_contDiffOn (a sign : ℝ) :
    ContDiffOn ℝ 2 (scalarPotential a sign) (Ioo (-1 : ℝ) 1) := by
  exact (contDiffOn_const.mul (contDiffOn_id.pow 2)).add
    (contDiffOn_const.mul bumpPrimitive_contDiffOn)

theorem scalarPotential_hasDerivAt (a sign : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (scalarPotential a sign) (a * u + sign * coordinateBump u) u := by
  convert (((hasDerivAt_id u).pow 2).const_mul (a / 2)).add
    ((bumpPrimitive_hasDerivAt hu).const_mul sign) using 1
  simp only [id_eq]
  ring

theorem scalarGradient_hasDerivAt (a sign : ℝ) {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => a * t + sign * coordinateBump t)
      (a + sign * modulusDerivative u) u := by
  simpa using ((hasDerivAt_id u).const_mul a).add
    ((coordinateBump_hasDerivAt hu).const_mul sign)

theorem scalarPotential_second_derivative (a sign : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    deriv (deriv (scalarPotential a sign)) u = a + sign * modulusDerivative u := by
  have hEq : deriv (scalarPotential a sign) =ᶠ[𝓝 u]
      (fun t => a * t + sign * coordinateBump t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hu] with t ht
    exact (scalarPotential_hasDerivAt a sign ht).deriv
  exact ((scalarGradient_hasDerivAt a sign hu).congr_of_eventuallyEq hEq).deriv

/-- Rectangle on which the separable construction is C². -/
def constructionDomain (sigma : ℝ) : Set (ℝ × ℝ) :=
  {z | z.1 ∈ Ioo (-1 : ℝ) 1 ∧ z.2 / sigma ∈ Ioo (-1 : ℝ) 1}

/-- Actual two-coordinate objective, written using its scalar primitives. -/
def separableObjective (a b sigma : ℝ) (z : ℝ × ℝ) : ℝ :=
  scalarPotential a (-1) z.1 + sigma ^ 2 * scalarPotential b 1 (z.2 / sigma)

/-- Joint C² regularity on an open neighborhood of the origin. -/
theorem separableObjective_contDiffOn (a b sigma : ℝ) :
    ContDiffOn ℝ 2 (separableObjective a b sigma) (constructionDomain sigma) := by
  have hu : ContDiffOn ℝ 2 (fun z : ℝ × ℝ => scalarPotential a (-1) z.1)
      (constructionDomain sigma) := (scalarPotential_contDiffOn a (-1)).comp
    (contDiff_fst.contDiffOn) (fun z (hz : z ∈ constructionDomain sigma) => hz.1)
  have hv : ContDiffOn ℝ 2 (fun z : ℝ × ℝ => scalarPotential b 1 (z.2 / sigma))
      (constructionDomain sigma) := (scalarPotential_contDiffOn b 1).comp
    (contDiff_snd.contDiffOn.div_const sigma) (fun z (hz : z ∈ constructionDomain sigma) => hz.2)
  exact hu.add (contDiffOn_const.mul hv)

/-- The first coordinate of the genuine gradient. -/
theorem separableObjective_partial_first (a b sigma : ℝ) {u v : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => separableObjective a b sigma (t,v))
      ((a - logModulus u) * u) u := by
  convert (scalarPotential_hasDerivAt a (-1) hu).add_const
    (sigma ^ 2 * scalarPotential b 1 (v / sigma)) using 1
  simp only [coordinateBump]
  ring

/-- The second coordinate of the genuine gradient. -/
theorem separableObjective_partial_second (a b : ℝ) {sigma u v : ℝ}
    (hsigma : sigma ≠ 0) (hv : v / sigma ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => separableObjective a b sigma (u,t))
      ((b + logModulus (v / sigma)) * v) v := by
  have h := (((scalarPotential_hasDerivAt b 1 hv).comp v
    ((hasDerivAt_id v).div_const sigma)).const_mul (sigma ^ 2)).const_add
      (scalarPotential a (-1) u)
  convert h using 1
  simp only [coordinateBump]
  field_simp
  <;> ring

/-- The two scalar diagonal Hessian entries of the construction. -/
theorem separableGradient_derivative_first (a : ℝ) {u : ℝ}
    (hu : u ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => (a - logModulus t) * t)
      (a - modulusDerivative u) u := by
  convert scalarGradient_hasDerivAt a (-1) hu using 1
  · ext t
    simp only [coordinateBump]
    ring
  · ring

theorem separableGradient_derivative_second (b : ℝ) {sigma v : ℝ}
    (hsigma : sigma ≠ 0) (hv : v / sigma ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t => (b + logModulus (t / sigma)) * t)
      (b + modulusDerivative (v / sigma)) v := by
  have h := (((scalarGradient_hasDerivAt b 1 hv).comp v
    ((hasDerivAt_id v).div_const sigma)).const_mul sigma)
  convert h using 1
  · ext t
    simp only [coordinateBump]
    field_simp
    <;> ring
  · field_simp
    <;> ring

@[simp] theorem logModulus_abs (x : ℝ) : logModulus |x| = logModulus x := by
  simp only [logModulus, Real.log_abs]

theorem modulusDerivative_nonneg {x : ℝ} (hx : |x| < 1) : 0 ≤ modulusDerivative x := by
  have hh : 0 ≤ logModulus x := by
    by_cases hzero : x = 0
    · simp [hzero]
    · rw [← logModulus_abs]
      exact (logModulus_pos (abs_pos.mpr hzero) hx).le
  exact add_nonneg hh (sq_nonneg _)

/-- A single neighborhood has positive diagonal Hessian bounds. -/
theorem exists_small_hessian_radius {a : ℝ} (ha : 0 < a) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x : ℝ, |x| < r →
      0 ≤ modulusDerivative x ∧ modulusDerivative x < a / 2 := by
  have hd : ContinuousAt modulusDerivative 0 :=
    logModulus_continuousAt_zero.add (logModulus_continuousAt_zero.pow 2)
  have hpos : modulusDerivative 0 < a / 2 := by simp; linarith
  obtain ⟨eps, heps, hnear⟩ := Metric.eventually_nhds_iff.mp
    (hd.tendsto.eventually (gt_mem_nhds hpos))
  refine ⟨min eps (1/2), lt_min heps (by norm_num), ?_, ?_⟩
  · exact (min_le_right _ _).trans_lt (by norm_num)
  · intro x hx
    have hx₁ : |x| < 1 := hx.trans ((min_le_right _ _).trans_lt (by norm_num))
    refine ⟨modulusDerivative_nonneg hx₁, ?_⟩
    apply hnear
    simpa [Real.dist_eq] using hx.trans_le (min_le_left _ _)

/-- Nonnegative second derivative gives convexity of a scalar potential. -/
theorem scalarPotential_convexOn {a sign r : ℝ} (hr : r ≤ 1)
    (hsecond : ∀ x : ℝ, |x| < r → 0 ≤ a + sign * modulusDerivative x) :
    ConvexOn ℝ (Ioo (-r) r) (scalarPotential a sign) := by
  have hsub : Ioo (-r) r ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    constructor <;> linarith [hx.1, hx.2]
  apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Ioo _ _)
    ((scalarPotential_contDiffOn a sign).continuousOn.mono hsub)
    (f' := fun x => a * x + sign * coordinateBump x)
    (f'' := fun x => a + sign * modulusDerivative x)
  · intro x hx
    exact (scalarPotential_hasDerivAt a sign (hsub (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    exact (scalarGradient_hasDerivAt a sign (hsub (interior_subset hx))).hasDerivWithinAt
  · intro x hx
    have hx' : x ∈ Ioo (-r) r := interior_subset hx
    exact hsecond x (abs_lt.mpr hx')

/-- Explicit Euclidean strong-convexity inequality; the squared Euclidean
coordinate distance is written out to avoid the product space's sup norm. -/
def EuclideanStrongConvexOn (s : Set (ℝ × ℝ)) (m : ℝ) (f : (ℝ × ℝ) → ℝ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t * x.1 + (1-t) * y.1, t * x.2 + (1-t) * y.2) ≤
      t * f x + (1-t) * f y -
        (m / 2) * t * (1-t) * ((x.1-y.1)^2 + (x.2-y.2)^2)

def smallRectangle (sigma r : ℝ) : Set (ℝ × ℝ) :=
  {z | |z.1| < r ∧ |z.2 / sigma| < r}

/-- Strong convexity of the actual two-variable objective near zero. -/
theorem separableObjective_strongConvex {a b sigma r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hsigma : sigma ≠ 0) (hr : r ≤ 1)
    (hd : ∀ x : ℝ, |x| < r →
      0 ≤ modulusDerivative x ∧ modulusDerivative x ≤ a / 2) :
    EuclideanStrongConvexOn (smallRectangle sigma r) (a / 2)
      (separableObjective a b sigma) := by
  have hf := scalarPotential_convexOn (a := a - a/2) (sign := -1) hr
    (fun x hx => by have := (hd x hx).2; linarith)
  have hg := scalarPotential_convexOn (a := b - a/2) (sign := 1) hr
    (fun x hx => by have := (hd x hx).1; linarith)
  intro x hx y hy t ht ht₁
  have htx := hf.2 (abs_lt.mp hx.1) (abs_lt.mp hy.1) ht
    (show 0 ≤ 1-t by linarith) (show t+(1-t)=1 by ring)
  have hty := hg.2 (abs_lt.mp hx.2) (abs_lt.mp hy.2) ht
    (show 0 ≤ 1-t by linarith) (show t+(1-t)=1 by ring)
  simp only [smul_eq_mul] at htx hty
  have hty' := mul_le_mul_of_nonneg_left hty (sq_nonneg sigma)
  let Fm : (ℝ × ℝ) → ℝ := fun z =>
    scalarPotential (a-a/2) (-1) z.1 + sigma^2 * scalarPotential (b-a/2) 1 (z.2/sigma)
  have hcorr (z : ℝ × ℝ) : Fm z = separableObjective a b sigma z -
      (a/4) * (z.1^2 + z.2^2) := by
    dsimp [Fm, separableObjective, scalarPotential]
    field_simp
    <;> ring
  let z : ℝ × ℝ := (t*x.1 + (1-t)*y.1, t*x.2 + (1-t)*y.2)
  have hv : z.2 / sigma = t * (x.2 / sigma) + (1-t) * (y.2 / sigma) := by
    dsimp [z]
    ring
  have hcomb : Fm z ≤ t * Fm x + (1-t) * Fm y := by
    dsimp [Fm]
    rw [hv]
    convert add_le_add htx hty' using 1 <;> dsimp [z] <;> ring
  rw [hcorr z, hcorr x, hcorr y] at hcomb
  change separableObjective a b sigma z ≤ _
  have hid : (t * separableObjective a b sigma x +
      (1-t) * separableObjective a b sigma y -
      ((a/2)/2) * t * (1-t) * ((x.1-y.1)^2 + (x.2-y.2)^2)) -
      separableObjective a b sigma z =
      (t * (separableObjective a b sigma x - (a/4)*(x.1^2+x.2^2)) +
      (1-t) * (separableObjective a b sigma y - (a/4)*(y.1^2+y.2^2))) -
      (separableObjective a b sigma z - (a/4)*(z.1^2+z.2^2)) := by
    dsimp [z]
    ring
  apply sub_nonneg.mp
  rw [hid]
  exact sub_nonneg.mpr hcomb

end
end BB.Counterexample
