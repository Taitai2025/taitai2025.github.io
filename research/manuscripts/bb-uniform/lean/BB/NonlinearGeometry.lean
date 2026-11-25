import BB.FrozenMap
import BB.LocalBootstrap

/-! # Local derivative bounds, actual secants, and pair perturbations

The hypotheses in `GradientControl` concern only the gradient, its genuine
Fréchet derivative, the frozen operator, and a scalar modulus.  The pair
recurrence and its perturbation estimate are conclusions.
-/

noncomputable section
set_option maxHeartbeats 400000
namespace BB.Local

open Set Metric
open BB.Secant BB.Gluing

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure GradientControl (g : E → E) (D : E → E →L[ℝ] E)
    (H : E →L[ℝ] E) (a b R : ℝ) (omega : ℝ → ℝ) : Prop where
  a_pos : 0 < a
  a_le_b : a ≤ b
  radius_pos : 0 < R
  zero : g 0 = 0
  derivative : ∀ x, ‖x‖ < R → HasFDerivAt g (D x) x
  modulus : ∀ x, ‖x‖ < R → ‖D x-H‖ ≤ omega ‖x‖
  coercive : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ
  operator_bound : ‖H‖ ≤ b
  monotone : Monotone omega
  nonnegative : ∀ t, 0 ≤ t → 0 ≤ omega t
  small : omega R ≤ a/2

variable {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
  {a b R : ℝ} {omega : ℝ → ℝ}

theorem GradientControl.chord (C : GradientControl g D H a b R omega)
    {x y : E} (hx : ‖x‖ < R) (hy : ‖y‖ < R) :
    ‖g y-g x-H (y-x)‖ ≤ (a/2)*‖y-x‖ := by
  apply BB.Secant.chord_error H (convex_ball (0 : E) R)
    (fun z hz => C.derivative z (by simpa [mem_ball,dist_zero_right] using hz))
    (fun z hz => (C.modulus z (by simpa [mem_ball,dist_zero_right] using hz)).trans
      ((C.monotone (le_of_lt (by simpa [mem_ball,dist_zero_right] using hz))).trans C.small))
    (by simpa [mem_ball,dist_zero_right] using hx)
    (by simpa [mem_ball,dist_zero_right] using hy)

theorem GradientControl.norm_equivalence (C : GradientControl g D H a b R omega)
    {x : E} (hx : ‖x‖ < R) :
    (a/2)*‖x‖ ≤ ‖g x‖ ∧ ‖g x‖ ≤ (b+a/2)*‖x‖ := by
  have he : ‖g x-H x‖ ≤ (a/2)*‖x‖ := by
    simpa [C.zero] using C.chord (x := 0) (by simpa using C.radius_pos) hx
  have hH : ‖H x‖ ≤ b*‖x‖ :=
    (H.le_opNorm x).trans (mul_le_mul_of_nonneg_right C.operator_bound (norm_nonneg x))
  have hl : a*‖x‖ ≤ ‖H x‖ := by
    by_cases hzero : x=0
    · simp [hzero]
    · exact BB.Secant.norm_lower_of_inner C.a_pos hzero (C.coercive x)
  constructor
  · have ht : ‖H x‖ ≤ ‖g x‖+‖g x-H x‖ := by
      have ht := norm_sub_le (g x) (g x-H x)
      have hid : g x-(g x-H x)=H x := by abel
      rwa [hid] at ht
    nlinarith only [he,hl,ht]
  · have ht : ‖g x‖ ≤ ‖H x‖+‖g x-H x‖ := by
      have ht := norm_add_le (H x) (g x-H x)
      have hid : H x+(g x-H x)=g x := by abel
      rwa [hid] at ht
    nlinarith only [he,hH,ht]

theorem GradientControl.point_bound (C : GradientControl g D H a b R omega)
    {x : E} (hx : ‖x‖ < R) : ‖x‖ ≤ (2/a)*‖g x‖ := by
  have h := (C.norm_equivalence hx).1
  calc
    ‖x‖ ≤ ‖g x‖/(a/2) := (le_div_iff (half_pos C.a_pos)).2 (by nlinarith only [h])
    _ = (2/a)*‖g x‖ := by ring

theorem GradientControl.gradient_ratio (C : GradientControl g D H a b R omega)
    {x y : E} {alpha A : ℝ} (hx : ‖x‖ < R) (hy : ‖y‖ < R)
    (hstep : y=x-alpha • g x) (halpha : 0 ≤ alpha) (hbound : alpha ≤ A) :
    ‖g y‖ ≤ (1+(b+a/2)*A)*‖g x‖ := by
  have hdiff : y-x= -alpha • g x := by rw [hstep,neg_smul]; abel
  have hH : ‖H (y-x)‖ ≤ b*‖y-x‖ :=
    (H.le_opNorm _).trans (mul_le_mul_of_nonneg_right C.operator_bound (norm_nonneg _))
  have he := C.chord hx hy
  have hch : ‖g y-g x‖ ≤ (b+a/2)*‖y-x‖ := by
    have ht := norm_add_le (H (y-x)) (g y-g x-H (y-x))
    have hid : H (y-x)+(g y-g x-H (y-x))=g y-g x := by abel
    rw [hid] at ht
    nlinarith only [he,hH,ht]
  rw [hdiff,norm_smul,Real.norm_eq_abs,abs_neg,abs_of_nonneg halpha] at hch
  have ht := norm_add_le (g x) (g y-g x)
  have hid : g x+(g y-g x)=g y := by abel
  rw [hid] at ht
  have hb : 0 ≤ b+a/2 := by linarith only [C.a_pos,C.a_le_b]
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbound hb) (norm_nonneg (g x))
  nlinarith only [hch,ht,hm]

/-- Use an intersection of balls so that a small state controls the modulus,
while every derivative is still evaluated in the original local domain. -/
def chordDomain (R S : ℝ) : Set E := ball (0 : E) R ∩ closedBall (0 : E) S

theorem chordDomain_convex (R S : ℝ) : Convex ℝ (chordDomain (E := E) R S) :=
  (convex_ball 0 R).inter (convex_closedBall 0 S)

theorem mem_chordDomain {x : E} {S : ℝ} (hx : ‖x‖ < R) (hS : ‖x‖ ≤ S) :
    x ∈ chordDomain R S := by
  simpa [chordDomain,mem_ball,mem_closedBall,dist_zero_right] using And.intro hx hS

theorem GradientControl.localized_derivative (C : GradientControl g D H a b R omega)
    (S : ℝ) {x : E} (hx : x ∈ chordDomain R S) :
    ‖D x-H‖ ≤ omega (min R S) := by
  have hxr : ‖x‖ < R := by simpa [mem_ball,dist_zero_right] using hx.1
  have hxs : ‖x‖ ≤ S := by simpa [mem_closedBall,dist_zero_right] using hx.2
  exact (C.modulus x hxr).trans (C.monotone (le_min hxr.le hxs))

theorem GradientControl.localized_secant (C : GradientControl g D H a b R omega)
    {x y : E} {S : ℝ} (hS : 0 ≤ S)
    (hx : x ∈ chordDomain R S) (hy : y ∈ chordDomain R S) (hne : y ≠ x) :
    BB.Secant.Control a b (omega (min R S)) (y-x) (H (y-x)) (g y-g x) := by
  apply BB.Secant.control_of_derivative_bound H (chordDomain_convex R S)
    C.a_pos C.a_le_b (C.nonnegative _ (le_min C.radius_pos.le hS))
    ((C.monotone (min_le_left _ _)).trans C.small) C.coercive C.operator_bound
    (fun z hz => C.derivative z (by simpa [mem_ball,dist_zero_right] using hz.1))
    (fun z hz => C.localized_derivative S hz) hx hy hne

theorem GradientControl.secant (C : GradientControl g D H a b R omega)
    {x y : E} (hx : ‖x‖ < R) (hy : ‖y‖ < R) (hne : y ≠ x) :
    BB.Secant.Control a b (omega R) (y-x) (H (y-x)) (g y-g x) := by
  have h := C.localized_secant C.radius_pos.le
    (mem_chordDomain hx hx.le) (mem_chordDomain hy hy.le) hne
  simpa using h

/-- A nonzero previous gradient and a positive previous step make the actual
secant nonzero, even if the next gradient has vanished. -/
theorem secant_ne_zero {x y : E} {alpha : ℝ} (halpha : 0 < alpha)
    (hstep : y=x-alpha • g x) (hg : g x ≠ 0) : y ≠ x := by
  intro heq
  have hs : alpha • g x=0 := by rw [heq] at hstep; exact sub_eq_self.mp hstep.symm
  exact (smul_ne_zero halpha.ne' hg) hs

end BB.Local
