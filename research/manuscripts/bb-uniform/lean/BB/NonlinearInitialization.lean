import BB.NonlinearTheorem
import BB.RadiusChoice

/-! # Uniform first-step initialization for the nonlinear theorem -/

noncomputable section
namespace BB.Local

open Set Metric BB.Secant BB.Gluing MeasureTheory Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
  {a b R : ℝ} {omega : ℝ → ℝ}

/-- Uniform initialization depends on an upper bound on the first step only.
The initial step is allowed to be arbitrarily small and positive. -/
theorem GradientControl.uniform_initialization (C : GradientControl g D H a b R omega)
    {M c A₀ epsilon : ℝ} (V : Certificate (frozenMap H) (pairCone (E := E) M) c)
    (hA₀ : 0 < A₀) (hepsilon : 0 < epsilon)
    (hM : 1+(b+a/2)*A₀ ≤ M) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ x : E, ‖x‖ < delta → ∀ alpha : ℝ,
      0 < alpha → alpha ≤ A₀ →
      ‖x‖ < R ∧ ‖x-alpha • g x‖ < R ∧
      (g x,g (x-alpha • g x)) ∈ pairCone M ∧
      V.value (g x,g (x-alpha • g x)) ≤ epsilon ∧
      V.value (g x,g (x-alpha • g x)) ≤
        V.prefactor*(1+(b+a/2)*A₀)*‖g x‖ := by
  let L := b+a/2
  let F := 1+L*A₀
  let P := V.prefactor*F*L
  have ha := C.a_pos
  have hb := ha.trans_le C.a_le_b
  have hL : 0 < L := by dsimp [L]; positivity
  have hF1 : 1 ≤ F := by dsimp [F]; nlinarith only [hL,hA₀]
  have hF : 0 < F := lt_of_lt_of_le zero_lt_one hF1
  have hVp : 0 < V.prefactor := lt_of_lt_of_le zero_lt_one V.prefactor_ge_one
  have hP : 0 < P := mul_pos (mul_pos hVp hF) hL
  refine ⟨min (R/F) (epsilon/P),lt_min (div_pos C.radius_pos hF) (div_pos hepsilon hP),?_⟩
  intro x hx alpha halpha hbound
  have hxRdiv : ‖x‖ < R/F := hx.trans_le (min_le_left _ _)
  have hxEdiv : ‖x‖ < epsilon/P := hx.trans_le (min_le_right _ _)
  have hxR : ‖x‖ < R := hxRdiv.trans_le <| (div_le_iff hF).2
    (le_mul_of_one_le_right C.radius_pos.le hF1)
  have hgrad : ‖g x‖ ≤ L*‖x‖ := (C.norm_equivalence hxR).2
  have hfirst : ‖x-alpha • g x‖ ≤ F*‖x‖ := by
    have ht := norm_sub_le x (alpha • g x)
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos halpha] at ht
    have hm := mul_le_mul hbound hgrad (norm_nonneg _) hA₀.le
    dsimp [F]
    nlinarith only [ht,hm]
  have hyR : ‖x-alpha • g x‖ < R := hfirst.trans_lt <| by
    have hh := (lt_div_iff hF).mp hxRdiv
    simpa only [mul_comm] using hh
  have hgratio : ‖g (x-alpha • g x)‖ ≤ F*‖g x‖ :=
    C.gradient_ratio hxR hyR rfl halpha.le hbound
  have hcone : (g x,g (x-alpha • g x)) ∈ pairCone M :=
    hgratio.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hnorm : ‖(g x,g (x-alpha • g x))‖ ≤ F*‖g x‖ := by
    exact max_le (le_mul_of_one_le_left (norm_nonneg _) hF1) hgratio
  have hvalue : V.value (g x,g (x-alpha • g x)) ≤ V.prefactor*F*‖g x‖ := by
    calc
      _ ≤ V.prefactor*‖(g x,g (x-alpha • g x))‖ := V.upper _ hcone
      _ ≤ V.prefactor*(F*‖g x‖) := mul_le_mul_of_nonneg_left hnorm hVp.le
      _ = _ := by ring
  refine ⟨hxR,hyR,hcone,?_,hvalue⟩
  calc
    V.value (g x,g (x-alpha • g x)) ≤ V.prefactor*F*‖g x‖ := hvalue
    _ ≤ V.prefactor*F*(L*‖x‖) := mul_le_mul_of_nonneg_left hgrad (mul_pos hVp hF).le
    _ = P*‖x‖ := by dsimp [P]; ring
    _ ≤ epsilon := by simpa only [mul_comm] using ((lt_div_iff hP).mp hxEdiv).le

end BB.Local
