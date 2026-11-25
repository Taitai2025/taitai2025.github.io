import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic

noncomputable section
namespace BB.Secant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def bb1 (s y : E) : ℝ := ‖s‖^2 / ⟪s,y⟫_ℝ
def bb2 (s y : E) : ℝ := ⟪s,y⟫_ℝ / ‖y‖^2
def blend (η : ℝ) (s y : E) : ℝ := η*bb1 s y+(1-η)*bb2 s y

def quotientConstant (a b : ℝ) : ℝ := 4*(1+3*b/a)/a^2

/-- Local secant data compared to the frozen positive operator applied to s. -/
structure Control (a b δ : ℝ) (s h y : E) : Prop where
  a_pos : 0 < a
  a_le_b : a ≤ b
  delta_nonneg : 0 ≤ δ
  delta_le_half : δ ≤ a/2
  s_ne_zero : s ≠ 0
  coercive : a*‖s‖^2 ≤ ⟪s,h⟫_ℝ
  base_norm : ‖h‖ ≤ b*‖s‖
  error : ‖y-h‖ ≤ δ*‖s‖

/-- Coercivity of a secant inner product gives a lower norm bound. -/
theorem norm_lower_of_inner {m : ℝ} {s y : E} (hm : 0 < m) (hs : s ≠ 0)
    (hlow : m*‖s‖^2 ≤ ⟪s,y⟫_ℝ) : m*‖s‖ ≤ ‖y‖ := by
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have h := hlow.trans (real_inner_le_norm s y)
  apply (mul_le_mul_left hr).mp
  nlinarith only [h]

/-- Both secant BB endpoints are positive and bounded by the reciprocal curvature lower bound. -/
theorem positive_bounds {m : ℝ} {s y : E} (hm : 0 < m) (hs : s ≠ 0)
    (hlow : m*‖s‖^2 ≤ ⟪s,y⟫_ℝ) :
    0 < bb1 s y ∧ 0 < bb2 s y ∧ bb1 s y ≤ 1/m ∧ bb2 s y ≤ 1/m := by
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr hs
  have hsq : 0 < ‖s‖^2 := sq_pos_of_pos hr
  have hinner : 0 < ⟪s,y⟫_ℝ := (mul_pos hm hsq).trans_le hlow
  have hny : m*‖s‖ ≤ ‖y‖ := norm_lower_of_inner hm hs hlow
  have hyp : 0 < ‖y‖ := (mul_pos hm hr).trans_le hny
  refine ⟨div_pos hsq hinner, div_pos hinner (sq_pos_of_pos hyp), ?_, ?_⟩
  · unfold bb1
    apply (div_le_div_iff hinner hm).2
    nlinarith only [hlow]
  · unfold bb2
    apply (div_le_div_iff (sq_pos_of_pos hyp) hm).2
    have h1 := mul_le_mul_of_nonneg_left (real_inner_le_norm s y) hm.le
    have h2 := mul_le_mul_of_nonneg_right hny hyp.le
    nlinarith only [h1,h2]

theorem Control.inner_error {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    |⟪s,y⟫_ℝ-⟪s,h⟫_ℝ| ≤ δ*‖s‖^2 := by
  rw [← inner_sub_right]
  calc
    |⟪s,y-h⟫_ℝ| ≤ ‖s‖*‖y-h‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖s‖*(δ*‖s‖) := mul_le_mul_of_nonneg_left C.error (norm_nonneg s)
    _ = δ*‖s‖^2 := by ring

theorem Control.actual_coercive {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    (a/2)*‖s‖^2 ≤ ⟪s,y⟫_ℝ := by
  have he := (abs_le.mp C.inner_error).1
  have hd := mul_le_mul_of_nonneg_right C.delta_le_half (sq_nonneg ‖s‖)
  nlinarith only [C.coercive,he,hd]

theorem Control.base_bounds {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    0 < bb1 s h ∧ 0 < bb2 s h ∧ bb1 s h ≤ 1/a ∧ bb2 s h ≤ 1/a :=
  positive_bounds C.a_pos C.s_ne_zero C.coercive

theorem Control.actual_bounds {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    0 < bb1 s y ∧ 0 < bb2 s y ∧ bb1 s y ≤ 2/a ∧ bb2 s y ≤ 2/a := by
  have h := positive_bounds (half_pos C.a_pos) C.s_ne_zero C.actual_coercive
  have hid : (1:ℝ)/(a/2)=2/a := by ring
  simpa only [hid] using h

theorem Control.actual_norm_upper {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    ‖y‖ ≤ (b+δ)*‖s‖ := by
  calc
    ‖y‖ = ‖h+(y-h)‖ := by congr 1; abel
    _ ≤ ‖h‖+‖y-h‖ := norm_add_le _ _
    _ ≤ b*‖s‖+δ*‖s‖ := add_le_add C.base_norm C.error
    _ = (b+δ)*‖s‖ := by ring

theorem Control.norm_square_error {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    |‖y‖^2-‖h‖^2| ≤ 3*b*δ*‖s‖^2 := by
  have hd : δ ≤ b := by linarith only [C.delta_le_half,C.a_pos,C.a_le_b]
  have hdiff : |‖y‖-‖h‖| ≤ δ*‖s‖ := (abs_norm_sub_norm_le y h).trans C.error
  have hsum : ‖y‖+‖h‖ ≤ 3*b*‖s‖ := by
    have hd' := mul_le_mul_of_nonneg_right hd (norm_nonneg s)
    nlinarith only [C.actual_norm_upper,C.base_norm,hd']
  rw [sq_sub_sq,abs_mul,abs_of_nonneg (add_nonneg (norm_nonneg y) (norm_nonneg h))]
  rw [mul_comm (‖y‖+‖h‖) |‖y‖-‖h‖|]
  calc
    |‖y‖-‖h‖| *(‖y‖+‖h‖) ≤ (δ*‖s‖)*(3*b*‖s‖) :=
      mul_le_mul hdiff hsum (add_nonneg (norm_nonneg y) (norm_nonneg h))
        (mul_nonneg C.delta_nonneg (norm_nonneg s))
    _ = 3*b*δ*‖s‖^2 := by ring

/-- A useful exact quotient-difference identity; no perturbation estimate is assumed. -/
theorem ratio_difference_mul (N N0 D D0 : ℝ) (hD : D ≠ 0) (hD0 : D0 ≠ 0) :
    (N/D-N0/D0)*D=(N-N0)+(N0/D0)*(D0-D) := by
  field_simp
  <;> ring


/-- Cancel the nonzero secant scale from a relative quotient estimate. -/
theorem cancel_secant_scale {e m F r : ℝ} (hm : 0 < m) (hr : 0 < r)
    (h : e*(m*r^2) ≤ F*r^2) : e ≤ F/m := by
  apply (le_div_iff hm).2
  apply (mul_le_mul_right (sq_pos_of_pos hr)).mp
  nlinarith only [h]

theorem Control.bb1_close_sharp {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    |bb1 s y-bb1 s h| ≤ (2/a^2)*δ := by
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr C.s_ne_zero
  have hD : 0 < ⟪s,y⟫_ℝ := (mul_pos (half_pos C.a_pos) (sq_pos_of_pos hr)).trans_le C.actual_coercive
  have hD0 : 0 < ⟪s,h⟫_ℝ := (mul_pos C.a_pos (sq_pos_of_pos hr)).trans_le C.coercive
  have hid := ratio_difference_mul (‖s‖^2) (‖s‖^2) ⟪s,y⟫_ℝ ⟪s,h⟫_ℝ hD.ne' hD0.ne'
  have hmain : |bb1 s y-bb1 s h| * ⟪s,y⟫_ℝ ≤ ((1/a)*δ)*‖s‖^2 := by
    calc
      |bb1 s y-bb1 s h| * ⟪s,y⟫_ℝ = |(bb1 s y-bb1 s h)*⟪s,y⟫_ℝ| := by
        rw [abs_mul,abs_of_pos hD]
      _ = |bb1 s h*(⟪s,h⟫_ℝ-⟪s,y⟫_ℝ)| := by
        unfold bb1
        rw [hid,sub_self,zero_add]
      _ = bb1 s h * |⟪s,y⟫_ℝ-⟪s,h⟫_ℝ| := by
        rw [abs_mul,abs_of_pos C.base_bounds.1,abs_sub_comm]
      _ ≤ (1/a)*(δ*‖s‖^2) :=
        mul_le_mul C.base_bounds.2.2.1 C.inner_error (abs_nonneg _)
          (one_div_nonneg.mpr C.a_pos.le)
      _ = ((1/a)*δ)*‖s‖^2 := by ring
  have hlow := mul_le_mul_of_nonneg_left C.actual_coercive (abs_nonneg (bb1 s y-bb1 s h))
  have hcancel := cancel_secant_scale (half_pos C.a_pos) hr (hlow.trans hmain)
  calc
    |bb1 s y-bb1 s h| ≤ ((1/a)*δ)/(a/2) := hcancel
    _ = (2/a^2)*δ := by field_simp; ring

theorem Control.bb2_close {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    |bb2 s y-bb2 s h| ≤ quotientConstant a b*δ := by
  have hr : 0 < ‖s‖ := norm_pos_iff.mpr C.s_ne_zero
  have hn0 := norm_lower_of_inner C.a_pos C.s_ne_zero C.coercive
  have hn := norm_lower_of_inner (half_pos C.a_pos) C.s_ne_zero C.actual_coercive
  have hnp : 0 < ‖y‖ := (mul_pos (half_pos C.a_pos) hr).trans_le hn
  have hn0p : 0 < ‖h‖ := (mul_pos C.a_pos hr).trans_le hn0
  have hE : 0 < ‖y‖^2 := sq_pos_of_pos hnp
  have hE0 : 0 < ‖h‖^2 := sq_pos_of_pos hn0p
  have hid := ratio_difference_mul ⟪s,y⟫_ℝ ⟪s,h⟫_ℝ (‖y‖^2) (‖h‖^2) hE.ne' hE0.ne'
  have hmain : |bb2 s y-bb2 s h| * ‖y‖^2 ≤ ((1+3*b/a)*δ)*‖s‖^2 := by
    calc
      |bb2 s y-bb2 s h| * ‖y‖^2 = |(bb2 s y-bb2 s h)*‖y‖^2| := by
        rw [abs_mul,abs_of_pos hE]
      _ = |(⟪s,y⟫_ℝ-⟪s,h⟫_ℝ)+bb2 s h*(‖h‖^2-‖y‖^2)| := by
        unfold bb2
        rw [hid]
      _ ≤ |⟪s,y⟫_ℝ-⟪s,h⟫_ℝ| + |bb2 s h*(‖h‖^2-‖y‖^2)| := abs_add _ _
      _ = |⟪s,y⟫_ℝ-⟪s,h⟫_ℝ| + bb2 s h*|‖y‖^2-‖h‖^2| := by
        rw [abs_mul,abs_of_pos C.base_bounds.2.1,abs_sub_comm (‖h‖^2) (‖y‖^2)]
      _ ≤ δ*‖s‖^2+(1/a)*(3*b*δ*‖s‖^2) :=
        add_le_add C.inner_error (mul_le_mul C.base_bounds.2.2.2 C.norm_square_error
          (abs_nonneg _) (one_div_nonneg.mpr C.a_pos.le))
      _ = ((1+3*b/a)*δ)*‖s‖^2 := by ring
  have hlow : (a^2/4)*‖s‖^2 ≤ ‖y‖^2 := by
    have hh := mul_self_le_mul_self (mul_nonneg (half_pos C.a_pos).le hr.le) hn
    nlinarith only [hh]
  have hcoef : 0 < a^2/4 := div_pos (sq_pos_of_pos C.a_pos) (by norm_num)
  have hcancel := cancel_secant_scale hcoef hr
    ((mul_le_mul_of_nonneg_left hlow (abs_nonneg (bb2 s y-bb2 s h))).trans hmain)
  calc
    |bb2 s y-bb2 s h| ≤ ((1+3*b/a)*δ)/(a^2/4) := hcancel
    _ = quotientConstant a b*δ := by unfold quotientConstant; field_simp; ring

theorem quotientConstant_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < quotientConstant a b := by
  have hb : 0 < b := ha.trans_le hab
  unfold quotientConstant
  positivity

theorem Control.bb1_close {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    |bb1 s y-bb1 s h| ≤ quotientConstant a b*δ := by
  have hb : 0 ≤ b := (C.a_pos.trans_le C.a_le_b).le
  have hcoef : 2/a^2 ≤ quotientConstant a b := by
    unfold quotientConstant
    apply (div_le_div_right (sq_pos_of_pos C.a_pos)).2
    have hq : 0 ≤ 3*b/a := div_nonneg (mul_nonneg (by norm_num) hb) C.a_pos.le
    nlinarith only [hq]
  exact C.bb1_close_sharp.trans (mul_le_mul_of_nonneg_right hcoef C.delta_nonneg)

/-- Every secant-interval choice uses the same convex coefficient in the frozen model. -/
theorem Control.blend_close {a b δ η : ℝ} {s h y : E} (C : Control a b δ s h y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    |blend η s y-blend η s h| ≤ quotientConstant a b*δ := by
  have hηc : 0 ≤ 1-η := sub_nonneg.mpr hη1
  unfold blend
  rw [show η*bb1 s y+(1-η)*bb2 s y-(η*bb1 s h+(1-η)*bb2 s h) =
    η*(bb1 s y-bb1 s h)+(1-η)*(bb2 s y-bb2 s h) by ring]
  calc
    _ ≤ |η*(bb1 s y-bb1 s h)|+|(1-η)*(bb2 s y-bb2 s h)| := abs_add _ _
    _ = η*|bb1 s y-bb1 s h|+(1-η)*|bb2 s y-bb2 s h| := by
      rw [abs_mul,abs_mul,abs_of_nonneg hη0,abs_of_nonneg hηc]
    _ ≤ η*(quotientConstant a b*δ)+(1-η)*(quotientConstant a b*δ) :=
      add_le_add (mul_le_mul_of_nonneg_left C.bb1_close hη0)
        (mul_le_mul_of_nonneg_left C.bb2_close hηc)
    _ = quotientConstant a b*δ := by ring

theorem Control.blend_bounds {a b δ η : ℝ} {s h y : E} (C : Control a b δ s h y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) : 0 < blend η s y ∧ blend η s y ≤ 2/a := by
  have hηc : 0 ≤ 1-η := sub_nonneg.mpr hη1
  obtain ⟨h1,h2,h1b,h2b⟩ := C.actual_bounds
  unfold blend
  constructor
  · by_cases hη : η=0
    · simpa only [hη,zero_mul,sub_zero,one_mul,zero_add] using h2
    · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hη0 (Ne.symm hη)) h1)
        (mul_nonneg hηc h2.le)
  · have hb := add_le_add (mul_le_mul_of_nonneg_left h1b hη0) (mul_le_mul_of_nonneg_left h2b hηc)
    nlinarith only [hb]


/-- Scale invariance cancels a previous stepsize regardless of how small it is. -/
theorem bb1_smul (s y : E) {t : ℝ} (ht : t ≠ 0) : bb1 (t • s) (t • y)=bb1 s y := by
  unfold bb1
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left,real_inner_smul_right]
  rw [show t*(t*⟪s,y⟫_ℝ)=t^2*⟪s,y⟫_ℝ by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

theorem bb2_smul (s y : E) {t : ℝ} (ht : t ≠ 0) : bb2 (t • s) (t • y)=bb2 s y := by
  unfold bb2
  rw [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,real_inner_smul_left,real_inner_smul_right]
  rw [show t*(t*⟪s,y⟫_ℝ)=t^2*⟪s,y⟫_ℝ by ring]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

theorem blend_smul (η : ℝ) (s y : E) {t : ℝ} (ht : t ≠ 0) :
    blend η (t • s) (t • y)=blend η s y := by
  unfold blend
  rw [bb1_smul s y ht,bb2_smul s y ht]

theorem frozen_blend_smul (H : E →L[ℝ] E) (η : ℝ) (u : E) {t : ℝ} (ht : t ≠ 0) :
    blend η (t • u) (H (t • u))=blend η u (H u) := by
  rw [map_smul,blend_smul η u (H u) ht]

/-- A genuine secant-interval step always has an interpolation coefficient in [0,1]. -/
theorem exists_blend_of_interval (s y : E) {α : ℝ}
    (hlo : bb2 s y ≤ α) (hhi : α ≤ bb1 s y) :
    ∃ η : ℝ, 0 ≤ η ∧ η ≤ 1 ∧ α=blend η s y := by
  by_cases heq : bb1 s y=bb2 s y
  · refine ⟨0,le_refl _,zero_le_one,?_⟩
    unfold blend
    simp only [zero_mul,sub_zero,one_mul,zero_add]
    exact le_antisymm (hhi.trans_eq heq) hlo
  · have hd : 0 < bb1 s y-bb2 s y := sub_pos.mpr (lt_of_le_of_ne (hlo.trans hhi) (Ne.symm heq))
    refine ⟨(α-bb2 s y)/(bb1 s y-bb2 s y), div_nonneg (sub_nonneg.mpr hlo) hd.le, ?_, ?_⟩
    · apply (div_le_one hd).2
      linarith only [hhi]
    · unfold blend
      field_simp
      <;> ring

/-- The actual and frozen intervals are compared with the SAME coefficient η. -/
theorem Control.blend_close_previous_gradient {a b δ η t : ℝ} {s u y : E}
    (H : E →L[ℝ] E) (C : Control a b δ s (H s) y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht : t ≠ 0) (hs : s=t • u) :
    |blend η s y-blend η u (H u)| ≤ quotientConstant a b*δ := by
  have h := C.blend_close hη0 hη1
  have hid : blend η s (H s)=blend η u (H u) := by
    rw [hs,frozen_blend_smul H η u ht]
  rwa [hid] at h

/-- Derivative continuity produces the needed chord estimate without commutation or Hessian integration. -/
theorem chord_error {g : E → E} {D : E → E →L[ℝ] E} (H : E →L[ℝ] E)
    {U : Set E} (hU : Convex ℝ U) {δ : ℝ}
    (hg : ∀ z ∈ U, HasFDerivAt g (D z) z)
    (hD : ∀ z ∈ U, ‖D z-H‖ ≤ δ) {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    ‖g y-g x-H (y-x)‖ ≤ δ*‖y-x‖ := by
  have hh : ∀ z ∈ U, HasFDerivWithinAt (fun z => g z-H z) (D z-H) U z := by
    intro z hz
    exact ((hg z hz).sub H.hasFDerivAt).hasFDerivWithinAt
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hh hD hU hx hy
  have hid : (g y-H y)-(g x-H x)=g y-g x-H (y-x) := by
    rw [map_sub]
    abel
  rwa [hid] at h

/-- Secant control for an actual differentiable gradient and a frozen coercive operator. -/
theorem control_of_derivative_bound {g : E → E} {D : E → E →L[ℝ] E}
    (H : E →L[ℝ] E) {U : Set E} (hU : Convex ℝ U) {a b δ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hd : 0 ≤ δ) (hdhalf : δ ≤ a/2)
    (hcoer : ∀ s : E, a*‖s‖^2 ≤ ⟪s,H s⟫_ℝ) (hH : ‖H‖ ≤ b)
    (hg : ∀ z ∈ U, HasFDerivAt g (D z) z) (hD : ∀ z ∈ U, ‖D z-H‖ ≤ δ)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) (hne : y ≠ x) :
    Control a b δ (y-x) (H (y-x)) (g y-g x) where
  a_pos := ha
  a_le_b := hab
  delta_nonneg := hd
  delta_le_half := hdhalf
  s_ne_zero := sub_ne_zero.mpr hne
  coercive := hcoer _
  base_norm := (H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _))
  error := chord_error H hU hg hD hx hy

/-- The next gradient step has the frozen linearization error prescribed by the derivative modulus. -/
theorem gradient_step_error {g : E → E} {D : E → E →L[ℝ] E} (H : E →L[ℝ] E)
    {U : Set E} (hU : Convex ℝ U) {δ α : ℝ}
    (hg : ∀ z ∈ U, HasFDerivAt g (D z) z) (hD : ∀ z ∈ U, ‖D z-H‖ ≤ δ)
    {x v : E} (hx : x ∈ U) (hy : x-α • v ∈ U) (hv : g x=v) :
    ‖g (x-α • v)-v+α • (H v)‖ ≤ δ * |α| * ‖v‖ := by
  have h := chord_error H hU hg hD hx hy
  have hd : (x-α • v)-x= -α • v := by rw [neg_smul]; abel
  rw [hd,map_smul,hv,norm_smul,Real.norm_eq_abs,abs_neg] at h
  have heq : g (x-α • v)-v-(-α) • H v=g (x-α • v)-v+α • H v := by
    rw [neg_smul,sub_neg_eq_add]
  rw [heq] at h
  nlinarith only [h]

/-- A direct one-step comparison once the scalar stepsizes and gradient chord are controlled. -/
theorem one_step_error {H : E →L[ℝ] E} {v w : E} {α β b ε δ B : ℝ}
    (hb : 0 ≤ b) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hα : |α| ≤ B)
    (hclose : |α-β| ≤ ε) (hH : ‖H v‖ ≤ b*‖v‖)
    (hgrad : ‖w-v+α • H v‖ ≤ δ * |α| * ‖v‖) :
    ‖w-(v-β • H v)‖ ≤ (b*ε+B*δ)*‖v‖ := by
  have hid : w-(v-β • H v)=(w-v+α • H v)+(β-α) • H v := by
    rw [sub_smul]
    abel
  rw [hid]
  calc
    _ ≤ ‖w-v+α • H v‖+‖(β-α) • H v‖ := norm_add_le _ _
    _ = ‖w-v+α • H v‖ + |α-β| * ‖H v‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_sub_comm]
    _ ≤ δ * |α| * ‖v‖+ε*(b*‖v‖) := add_le_add hgrad
      (mul_le_mul hclose hH (norm_nonneg _) hε)
    _ ≤ δ*B*‖v‖+ε*(b*‖v‖) :=
      add_le_add_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hα hδ) (norm_nonneg _)) _
    _ = (b*ε+B*δ)*‖v‖ := by ring

/-- The true gradient pair differs from the frozen pair by a controlled relative error.
The product carries its standard maximum norm; the first components coincide. -/
theorem Control.next_pair_error {a b δ δ' η t : ℝ} {s u v w y : E}
    (H : E →L[ℝ] E) (C : Control a b δ s (H s) y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht : t ≠ 0) (hs : s=t • u)
    (hd' : 0 ≤ δ') (hH : ‖H v‖ ≤ b*‖v‖)
    (hgrad : ‖w-v+(blend η s y) • H v‖ ≤ δ' * |blend η s y| * ‖v‖) :
    ‖(v,w)-(v,v-(blend η u (H u)) • H v)‖ ≤
      (b*quotientConstant a b*δ+(2/a)*δ')*‖v‖ := by
  have hα := C.blend_bounds hη0 hη1
  have hα' : |blend η s y| ≤ 2/a := by
    rw [abs_of_pos hα.1]
    exact hα.2
  have hε : 0 ≤ quotientConstant a b*δ :=
    mul_nonneg (quotientConstant_pos C.a_pos C.a_le_b).le C.delta_nonneg
  have hh := one_step_error (C.a_pos.trans_le C.a_le_b).le hε hd' hα'
    (C.blend_close_previous_gradient H hη0 hη1 ht hs) hH hgrad
  have hp : ‖(v,w)-(v,v-(blend η u (H u)) • H v)‖ =
      ‖w-(v-(blend η u (H u)) • H v)‖ := by
    simp only [Prod.norm_def,Prod.fst_sub,Prod.snd_sub,sub_self,norm_zero]
    exact max_eq_right (norm_nonneg _)
  rw [hp]
  simpa only [mul_assoc] using hh

/-- Ready-to-use nonlinear pair perturbation: derivative control on the next chord
combines with actual secant quotient control and the previous gradient direction. -/
theorem Control.gradient_pair_error {g : E → E} {D : E → E →L[ℝ] E}
    (H : E →L[ℝ] E) {U : Set E} (hU : Convex ℝ U)
    {a b δ δ' η t : ℝ} {s u y x : E}
    (C : Control a b δ s (H s) y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (ht : t ≠ 0) (hs : s=t • u)
    (hd' : 0 ≤ δ') (hH : ‖H‖ ≤ b)
    (hg : ∀ z ∈ U, HasFDerivAt g (D z) z)
    (hD : ∀ z ∈ U, ‖D z-H‖ ≤ δ')
    (hx : x ∈ U) (hy : x-(blend η s y) • g x ∈ U) :
    ‖(g x,g (x-(blend η s y) • g x))-
      (g x,g x-(blend η u (H u)) • H (g x))‖ ≤
      (b*quotientConstant a b*δ+(2/a)*δ')*‖g x‖ := by
  exact C.next_pair_error H hη0 hη1 ht hs hd'
    ((H.le_opNorm _).trans (mul_le_mul_of_nonneg_right hH (norm_nonneg _)))
    (gradient_step_error H hU hg hD hx hy rfl)

end BB.Secant
