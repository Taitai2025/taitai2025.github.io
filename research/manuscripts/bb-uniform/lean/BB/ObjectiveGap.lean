import BB.NonlinearGeometry
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! # Genuine objective gaps and the C²-to-gradient interface -/

set_option autoImplicit false
noncomputable section
namespace BB.Local

open Set Metric InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- C² on the open neighborhood implies that the actual gradient is C¹ there. -/
theorem c2_gradient_contDiffOn {f : E → ℝ} {R : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball (0:E) R)) :
    ContDiffOn ℝ 1 (gradient f) (ball (0:E) R) := by
  have hd : ContDiffOn ℝ 1 (fderiv ℝ f) (ball (0:E) R) :=
    hf.fderiv_of_isOpen isOpen_ball (by norm_num)
  exact (toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn hd

/-- Both derivatives used in the local theorem are the genuine derivatives of f. -/
theorem c2_gradient_derivatives {f : E → ℝ} {R : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball (0:E) R)) {x : E} (hx : ‖x‖ < R) :
    HasGradientAt f (gradient f x) x ∧
      HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x := by
  have hmem : x ∈ ball (0:E) R := by simpa [mem_ball,dist_zero_right] using hx
  have hn := isOpen_ball.mem_nhds hmem
  constructor
  · exact ((hf.differentiableOn (by norm_num)).differentiableAt hn).hasGradientAt
  · exact (((c2_gradient_contDiffOn hf).differentiableOn (by norm_num)).differentiableAt hn).hasFDerivAt

variable {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
  {a b R : ℝ} {omega : ℝ → ℝ}

theorem smul_mem_local_ball (hR : 0 < R) {x : E} (hx : ‖x‖ < R)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) : ‖t • x‖ < R := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (norm_nonneg x) ht.2).trans_lt hx

/-- Radial inner-product bounds, obtained from the derivative modulus. -/
theorem GradientControl.radial_inner (C : GradientControl g D H a b R omega)
    {x : E} (hx : ‖x‖ < R) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    (a/2)*t*‖x‖^2 ≤ @inner ℝ _ _ (g (t • x)) x ∧
      @inner ℝ _ _ (g (t • x)) x ≤ (b+a/2)*t*‖x‖^2 := by
  have htx := smul_mem_local_ball C.radius_pos hx ht
  have he : ‖g (t • x)-H (t • x)‖ ≤ (a/2)*(t*‖x‖) := by
    have hh := C.chord (x := 0) (by simpa using C.radius_pos) htx
    simpa [C.zero,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] using hh
  have hie := abs_real_inner_le_norm (g (t • x)-H (t • x)) x
  have hie' := mul_le_mul_of_nonneg_right he (norm_nonneg x)
  have hl := mul_le_mul_of_nonneg_left (C.coercive x) ht.1
  have hinner : @inner ℝ _ _ (g (t • x)-H (t • x)) x =
      @inner ℝ _ _ (g (t • x)) x-t*@inner ℝ _ _ x (H x) := by
    rw [inner_sub_left,map_smul,real_inner_smul_left,real_inner_comm (H x) x]
  rw [hinner] at hie
  have hu := (C.norm_equivalence htx).2
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1] at hu
  have hu' := mul_le_mul_of_nonneg_right hu (norm_nonneg x)
  constructor
  · have hh := (abs_le.mp (hie.trans hie')).1
    nlinarith only [hh,hl]
  · have hh := real_inner_le_norm (g (t • x)) x
    nlinarith only [hh,hu']

/-- A one-variable radial derivative bound gives the precise quadratic
comparison constant by subtracting its quadratic primitive. -/
theorem radial_quadratic_lower {f : E → ℝ} {g : E → E} {R m : ℝ}
    (hR : 0 < R) (hf : ∀ x, ‖x‖ < R → HasGradientAt f (g x) x)
    {x : E} (hx : ‖x‖ < R)
    (hinner : ∀ t ∈ Icc (0:ℝ) 1, m*t*‖x‖^2 ≤ @inner ℝ _ _ (g (t • x)) x) :
    (m/2)*‖x‖^2 ≤ f x-f 0 := by
  let F : ℝ → ℝ := fun t => f (t • x)-(m/2)*t^2*‖x‖^2
  let F' : ℝ → ℝ := fun t => @inner ℝ _ _ (g (t • x)) x-m*t*‖x‖^2
  have hd : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt F (F' t) t := by
    intro t ht
    have hchain := (hf (t • x) (smul_mem_local_ball hR hx ht)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).smul_const x)
    have hp := (((hasDerivAt_id t).pow 2).const_mul (m/2)).mul_const (‖x‖^2)
    have hh := hchain.sub hp
    simp only [Function.comp_apply,id_eq,one_smul,toDual_apply,
      Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] at hh
    convert hh using 1 <;> dsimp [F,F'] <;> ring
  have hmono : MonotoneOn F (Icc (0:ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact sub_nonneg.mpr (hinner t (interior_subset ht))
  have hh := hmono (show (0:ℝ) ∈ Icc (0:ℝ) 1 by norm_num)
    (show (1:ℝ) ∈ Icc (0:ℝ) 1 by norm_num) (by norm_num : (0:ℝ) ≤ 1)
  simp only [F,zero_smul,one_smul,zero_pow (by norm_num : 2 ≠ 0),one_pow,
    mul_zero,zero_mul,sub_zero,mul_one] at hh
  linarith only [hh]

/-- The objective gap is bounded above and below by the squared distance,
using the actual gradient relation and local Hessian control. -/
theorem GradientControl.objective_gap (C : GradientControl g D H a b R omega)
    {f : E → ℝ} (hf : ∀ x, ‖x‖ < R → HasGradientAt f (g x) x)
    {x : E} (hx : ‖x‖ < R) :
    (a/4)*‖x‖^2 ≤ f x-f 0 ∧ f x-f 0 ≤ ((b+a/2)/2)*‖x‖^2 := by
  constructor
  · have hh := radial_quadratic_lower C.radius_pos hf hx
      (fun t ht => (C.radial_inner hx ht).1)
    convert hh using 1 <;> ring
  · have hneg : ∀ y, ‖y‖ < R → HasGradientAt (fun u => -f u) (-g y) y := by
      intro y hy
      simpa only [HasGradientAt,HasGradientAtFilter,map_neg] using (hf y hy).hasFDerivAt.neg
    have hh := radial_quadratic_lower (m := -(b+a/2)) C.radius_pos hneg hx (by
      intro t ht
      rw [inner_neg_left]
      nlinarith only [(C.radial_inner hx ht).2])
    nlinarith only [hh]

/-- Squaring an exact error estimate gives the exact squared objective factor. -/
theorem objective_rate_from_error {f : E → ℝ} {x : ℕ → E}
    {m L A c : ℝ} (hm : 0 < m) (hL : 0 ≤ L) (hA : 0 ≤ A) (hc : 0 ≤ c)
    (hlo : m*‖x 0‖^2 ≤ f (x 0)-f 0)
    (hhi : ∀ k, f (x k)-f 0 ≤ L*‖x k‖^2)
    (hrate : ∀ k, ‖x k‖ ≤ A*c^k*‖x 0‖) (k : ℕ) :
    f (x k)-f 0 ≤ (L*A^2/m)*c^(2*k)*(f (x 0)-f 0) := by
  have hnn : 0 ≤ A*c^k*‖x 0‖ := by positivity
  have hs : ‖x k‖^2 ≤ A^2*(c^k)^2*‖x 0‖^2 := by
    nlinarith [hrate k,norm_nonneg (x k)]
  have hs' := mul_le_mul_of_nonneg_left hs hL
  have hcoef : 0 ≤ L*A^2*(c^k)^2 := by positivity
  have hlow : ‖x 0‖^2 ≤ (f (x 0)-f 0)/m := (le_div_iff hm).mpr (by nlinarith only [hlo])
  have hh := mul_le_mul_of_nonneg_left hlow hcoef
  have he : (c^k)^2 = c^(2*k) := by rw [← pow_mul]; congr 1; omega
  rw [he] at hs' hh
  have hh' : L*(A^2*c^(2*k)*‖x 0‖^2) ≤ (L*A^2/m)*c^(2*k)*(f (x 0)-f 0) := by
    convert hh using 1 <;> ring
  exact (hhi k).trans (hs'.trans hh')

end BB.Local
