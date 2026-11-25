import BB.NonlinearGeometry

/-! # One actual nonlinear secant step and its frozen comparison -/

noncomputable section
namespace BB.Local

open Set Metric BB.Secant BB.Gluing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
  {a b R : ℝ} {omega : ℝ → ℝ}

/-- A choice from the actual secant interval, required only before termination. -/
def intervalChoice (g : E → E) (x y : E) (alpha : ℝ) : Prop :=
  g y ≠ 0 → bb2 (y-x) (g y-g x) ≤ alpha ∧ alpha ≤ bb1 (y-x) (g y-g x)

/-- The common radius used to control both the preceding and proposed chords. -/
def radiusFactor (a : ℝ) : ℝ := 4/a

/-- A relative perturbation constant independent of both interpolation coefficients
and the positive magnitude of the preceding step. -/
def perturbationFactor (a b : ℝ) : ℝ := b*quotientConstant a b+2/a

theorem radiusFactor_pos (ha : 0 < a) : 0 < radiusFactor a := by
  unfold radiusFactor
  positivity

theorem perturbationFactor_nonneg (ha : 0 < a) (hab : a ≤ b) :
    0 ≤ perturbationFactor a b := by
  have hb := ha.trans_le hab
  have hq := quotientConstant_pos ha hab
  unfold perturbationFactor
  positivity

theorem pair_norm_fst_le (u v : E) : ‖u‖ ≤ ‖(u,v)‖ := by
  exact le_max_left _ _
theorem pair_norm_snd_le (u v : E) : ‖v‖ ≤ ‖(u,v)‖ := by
  exact le_max_right _ _

theorem GradientControl.next_bound (C : GradientControl g D H a b R omega)
    {x y z : E} {alpha beta : ℝ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) (halpha : 0 < alpha)
    (hprev : y=x-alpha • g x) (hnext : z=y-beta • g y)
    (hchoice : intervalChoice g x y beta) :
    ‖z‖ ≤ radiusFactor a * ‖(g x,g y)‖ := by
  by_cases hcur : g y=0
  · have hzy : z=y := by simpa [hcur] using hnext
    have hp := C.point_bound hy
    rw [hcur,norm_zero,mul_zero] at hp
    rw [hzy]
    exact hp.trans (mul_nonneg (radiusFactor_pos C.a_pos).le (norm_nonneg _))
  · have hzero : g x ≠ 0 := by
      intro hxzero
      have hyx : y=x := by simpa [hxzero] using hprev
      exact hcur (by simpa only [hyx] using hxzero)
    have hs := C.secant hx hy (secant_ne_zero halpha hprev hzero)
    have hb0 : 0 < beta := hs.actual_bounds.2.1.trans_le (hchoice hcur).1
    have hb : beta ≤ 2/a := (hchoice hcur).2.trans hs.actual_bounds.2.2.1
    have hp := C.point_bound hy
    have ht := norm_sub_le y (beta • g y)
    rw [← hnext,norm_smul,Real.norm_eq_abs,abs_of_pos hb0] at ht
    have hm := mul_le_mul_of_nonneg_right hb (norm_nonneg (g y))
    calc
      ‖z‖ ≤ (4/a)*‖g y‖ := by
        rw [show 4/a=2/a+2/a by ring]
        nlinarith only [hp,ht,hm]
      _ ≤ radiusFactor a*‖(g x,g y)‖ :=
        mul_le_mul_of_nonneg_left (pair_norm_snd_le _ _) (radiusFactor_pos C.a_pos).le

theorem GradientControl.next_cone (C : GradientControl g D H a b R omega)
    {x y z : E} {alpha beta M : ℝ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) (hz : ‖z‖ < R) (halpha : 0 < alpha)
    (hprev : y=x-alpha • g x) (hnext : z=y-beta • g y)
    (hchoice : intervalChoice g x y beta)
    (hM : 1+(b+a/2)*(2/a) ≤ M) : (g y,g z) ∈ pairCone M := by
  by_cases hcur : g y=0
  · have hzy : z=y := by simpa [hcur] using hnext
    simp [pairCone,hzy,hcur]
  · have hzero : g x ≠ 0 := by
      intro hxzero
      have hyx : y=x := by simpa [hxzero] using hprev
      exact hcur (by simpa only [hyx] using hxzero)
    have hs := C.secant hx hy (secant_ne_zero halpha hprev hzero)
    have hb0 : 0 < beta := hs.actual_bounds.2.1.trans_le (hchoice hcur).1
    have hb : beta ≤ 2/a := (hchoice hcur).2.trans hs.actual_bounds.2.2.1
    exact (C.gradient_ratio hy hz hnext hb0.le hb).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg _))

/-- All nonlinear quotients and derivative remainders are derived from the actual
three iterates, rather than supplied as an assumed scalar recurrence. -/
theorem GradientControl.actual_pair_error (C : GradientControl g D H a b R omega)
    {x y z : E} {alpha beta : ℝ}
    (hx : ‖x‖ < R) (hy : ‖y‖ < R) (hz : ‖z‖ < R) (halpha : 0 < alpha)
    (hprev : y=x-alpha • g x) (hnext : z=y-beta • g y)
    (hchoice : intervalChoice g x y beta) :
    ∃ eta : Set.Icc (0 : ℝ) 1,
      ‖(g y,g z)-frozenMap H eta (g x,g y)‖ ≤
        perturbationFactor a b * omega (radiusFactor a*‖(g x,g y)‖) * ‖(g x,g y)‖ := by
  by_cases hcur : g y=0
  · have hzy : z=y := by simpa [hcur] using hnext
    refine ⟨⟨0,le_refl _,zero_le_one⟩,?_⟩
    have hRHS : 0 ≤ perturbationFactor a b *
        omega (radiusFactor a*‖(g x,g y)‖)*‖(g x,g y)‖ :=
      mul_nonneg (mul_nonneg (perturbationFactor_nonneg C.a_pos C.a_le_b)
        (C.nonnegative _ (mul_nonneg (radiusFactor_pos C.a_pos).le (norm_nonneg _))))
        (norm_nonneg _)
    simpa [hcur,hzy,frozenMap,Prod.norm_def] using hRHS
  · have hzero : g x ≠ 0 := by
      intro hxzero
      have hyx : y=x := by simpa [hxzero] using hprev
      exact hcur (by simpa only [hyx] using hxzero)
    let S := radiusFactor a*‖(g x,g y)‖
    have hS : 0 ≤ S := mul_nonneg (radiusFactor_pos C.a_pos).le (norm_nonneg _)
    have htwo : 0 ≤ 2/a := div_nonneg (by norm_num) C.a_pos.le
    have h24 : 2/a ≤ radiusFactor a := by unfold radiusFactor; apply div_le_div_of_nonneg_right (by norm_num) C.a_pos.le
    have hxr : ‖x‖ ≤ S := (C.point_bound hx).trans <| calc
      (2/a)*‖g x‖ ≤ (2/a)*‖(g x,g y)‖ := mul_le_mul_of_nonneg_left (pair_norm_fst_le _ _) htwo
      _ ≤ S := mul_le_mul_of_nonneg_right h24 (norm_nonneg _)
    have hyr : ‖y‖ ≤ S := (C.point_bound hy).trans <| calc
      (2/a)*‖g y‖ ≤ (2/a)*‖(g x,g y)‖ := mul_le_mul_of_nonneg_left (pair_norm_snd_le _ _) htwo
      _ ≤ S := mul_le_mul_of_nonneg_right h24 (norm_nonneg _)
    have hzr : ‖z‖ ≤ S := C.next_bound hx hy halpha hprev hnext hchoice
    have hxU := mem_chordDomain hx hxr
    have hyU := mem_chordDomain hy hyr
    have hzU := mem_chordDomain hz hzr
    have hs := C.localized_secant hS hxU hyU (secant_ne_zero halpha hprev hzero)
    obtain ⟨eta,heta0,heta1,hbeta⟩ := exists_blend_of_interval (y-x) (g y-g x)
      (hchoice hcur).1 (hchoice hcur).2
    have hdir : y-x= -alpha • g x := by rw [hprev,neg_smul]; abel
    have hd : 0 ≤ omega (min R S) := C.nonnegative _ (le_min C.radius_pos.le hS)
    have hzU' : y-blend eta (y-x) (g y-g x) • g y ∈ chordDomain R S := by
      rw [← hbeta,← hnext]
      exact hzU
    have hp := hs.gradient_pair_error H (chordDomain_convex R S) heta0 heta1
      (neg_ne_zero.mpr halpha.ne') hdir hd C.operator_bound
      (fun q hq => C.derivative q (by simpa [mem_ball,dist_zero_right] using hq.1))
      (fun q hq => C.localized_derivative S hq) hyU hzU'
    rw [← hbeta,← hnext] at hp
    refine ⟨⟨eta,heta0,heta1⟩,?_⟩
    change ‖(g y,g z)-(g y,g y-blend eta (g x) (H (g x)) • H (g y))‖ ≤ _
    calc
      _ ≤ (b*quotientConstant a b*omega (min R S)+(2/a)*omega (min R S))*‖g y‖ := hp
      _ = perturbationFactor a b*omega (min R S)*‖g y‖ := by unfold perturbationFactor; ring
      _ ≤ perturbationFactor a b*omega S*‖(g x,g y)‖ := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (C.monotone (min_le_right _ _))
            (perturbationFactor_nonneg C.a_pos C.a_le_b)
        · exact pair_norm_snd_le _ _
        · exact norm_nonneg _
        · exact mul_nonneg (perturbationFactor_nonneg C.a_pos C.a_le_b) (C.nonnegative _ hS)
      _ = _ := rfl

end BB.Local
