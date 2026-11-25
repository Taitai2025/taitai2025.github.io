import BB.NonlinearGeometry

noncomputable section
namespace BB.Secant

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cauchy--Schwarz orders the two genuine secant endpoints whenever the
secant curvature is positive. This does not require a quadratic objective. -/
theorem bb2_le_bb1 {s y : E} (hinner : 0 < ⟪s,y⟫_ℝ) : bb2 s y ≤ bb1 s y := by
  have hy : y ≠ 0 := by
    intro hy
    rw [hy,inner_zero_right] at hinner
    exact lt_irrefl _ hinner
  have hny : 0 < ‖y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
  unfold bb2 bb1
  apply (div_le_div_iff hny hinner).2
  have hcs := mul_self_le_mul_self hinner.le (real_inner_le_norm s y)
  nlinarith only [hcs]

theorem Control.endpoint_order {a b δ : ℝ} {s h y : E} (C : Control a b δ s h y) :
    bb2 s y ≤ bb1 s y := by
  have hr : 0 < ‖s‖^2 := sq_pos_of_pos (norm_pos_iff.mpr C.s_ne_zero)
  exact bb2_le_bb1 ((mul_pos (half_pos C.a_pos) hr).trans_le C.actual_coercive)

/-- Every convex blend is in the nonempty, positive actual secant interval. -/
theorem Control.blend_mem_interval {a b δ η : ℝ} {s h y : E} (C : Control a b δ s h y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    0 < blend η s y ∧ bb2 s y ≤ blend η s y ∧ blend η s y ≤ bb1 s y := by
  refine ⟨(C.blend_bounds hη0 hη1).1,?_,?_⟩
  · have hh := mul_nonneg hη0 (sub_nonneg.mpr C.endpoint_order)
    unfold blend
    nlinarith only [hh]
  · have hh := mul_nonneg (sub_nonneg.mpr hη1) (sub_nonneg.mpr C.endpoint_order)
    unfold blend
    nlinarith only [hh]

theorem Control.exists_positive_interval_choice {a b δ : ℝ} {s h y : E}
    (C : Control a b δ s h y) :
    ∃ α : ℝ, 0 < α ∧ bb2 s y ≤ α ∧ α ≤ bb1 s y ∧ α ≤ 2/a :=
  ⟨bb2 s y,C.actual_bounds.2.1,le_refl _,C.endpoint_order,C.actual_bounds.2.2.2⟩

end BB.Secant

namespace BB.Local
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The true secant interval is nonempty whenever distinct iterates lie in the
controlled neighborhood; its positivity is a conclusion of the derivative bounds. -/
theorem GradientControl.secant_interval_nonempty
    {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
    {a b R : ℝ} {omega : ℝ → ℝ} (C : GradientControl g D H a b R omega)
    {x y : E} (hx : ‖x‖ < R) (hy : ‖y‖ < R) (hne : y ≠ x) :
    ∃ α : ℝ, 0 < α ∧ BB.Secant.bb2 (y-x) (g y-g x) ≤ α ∧
      α ≤ BB.Secant.bb1 (y-x) (g y-g x) ∧ α ≤ 2/a :=
  (C.secant hx hy hne).exists_positive_interval_choice

end BB.Local
