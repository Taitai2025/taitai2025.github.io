import BB.NonlinearInitialization

/-! # Every larger local factor without the Dini integral -/

noncomputable section
namespace BB.Local

open Set Metric BB.Secant BB.Gluing MeasureTheory Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
  {a b R : ℝ} {omega : ℝ → ℝ}

/-- With only a modulus tending to zero, every prescribed factor strictly above
that of the frozen certificate is a uniform local rate for the actual algorithm. -/
theorem GradientControl.uniform_rough_rate_of_certificate
    (C : GradientControl g D H a b R omega)
    {M c A₀ gamma : ℝ} (V : Certificate (frozenMap H) (pairCone (E := E) M) c)
    (hc : 0 < c) (hcg : c < gamma) (hg1 : gamma < 1) (hA₀ : 0 < A₀)
    (hM0 : 1+(b+a/2)*A₀ ≤ M) (hM : 1+(b+a/2)*(2/a) ≤ M)
    (hlim : Tendsto omega (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0)) :
    ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧
      ∀ (x : ℕ → E) (alpha : ℕ → ℝ), ‖x 0‖ < delta →
        (∀ n, 0 < alpha n) → alpha 0 ≤ A₀ →
        (∀ n, x (n+1)=x n-alpha n • g (x n)) →
        (∀ n, intervalChoice g (x n) (x (n+1)) (alpha (n+1))) →
        (∀ n, ‖x n‖ < R) ∧
        (∀ n, g (x n) ≠ 0 →
          0 < ⟪x (n+1)-x n,g (x (n+1))-g (x n)⟫_ℝ ∧
          0 < ‖g (x (n+1))-g (x n)‖^2) ∧
        (∀ n, ‖g (x n)‖ ≤ K*gamma^n*‖g (x 0)‖) ∧
        (∀ n, ‖x n‖ ≤ K*gamma^n*‖x 0‖) := by
  have hgamma : 0 < gamma := hc.trans hcg
  obtain ⟨epsilon,hepsilon,hball,hsmall⟩ :=
    BB.RadiusChoice.exists_radius (D := V.lipConstant*perturbationFactor a b)
      omega hlim (radiusFactor_pos C.a_pos) C.radius_pos hcg
  obtain ⟨delta,hdelta,hinit⟩ := C.uniform_initialization V hA₀ hepsilon hM0
  let G := V.prefactor*(1+(b+a/2)*A₀)
  let K := max G ((2/a)*G*(b+a/2))
  have ha := C.a_pos
  have hb := ha.trans_le C.a_le_b
  have hF : 0 < 1+(b+a/2)*A₀ := by positivity
  have hVp : 0 < V.prefactor := lt_of_lt_of_le zero_lt_one V.prefactor_ge_one
  have hG : 0 < G := mul_pos hVp hF
  have hK : 0 < K := hG.trans_le (le_max_left _ _)
  refine ⟨delta,K,hdelta,hK,?_⟩
  intro x alpha hx halpha hA hstep hchoice
  obtain ⟨hx0,hx1,hcone0,hve,hvbound⟩ := hinit (x 0) hx (alpha 0) (halpha 0) hA
  rw [← hstep 0] at hx1 hcone0 hve hvbound
  obtain ⟨hstay,hcone,hv,_⟩ := C.local_bootstrap V hM x alpha halpha hstep hchoice
    hgamma.le hg1.le hx0 hx1 hcone0 hve hball hsmall
  have hgrad : ∀ n, ‖g (x n)‖ ≤ G*gamma^n*‖g (x 0)‖ := by
    intro n
    calc
      ‖g (x n)‖ ≤ ‖(g (x n),g (x (n+1)))‖ := pair_norm_fst_le _ _
      _ ≤ V.value (g (x n),g (x (n+1))) := V.lower _ (hcone n)
      _ ≤ gamma^n*V.value (g (x 0),g (x 1)) := hv n
      _ ≤ gamma^n*(V.prefactor*(1+(b+a/2)*A₀)*‖g (x 0)‖) :=
        mul_le_mul_of_nonneg_left hvbound (pow_nonneg hgamma.le n)
      _ = G*gamma^n*‖g (x 0)‖ := by dsimp [G]; ring
  refine ⟨hstay,?_,?_,?_⟩
  · intro n hzero
    exact C.secant_denominators (hstay n) (hstay (n+1)) (halpha n) (hstep n) hzero
  · intro n
    exact (hgrad n).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hgamma.le n)) (norm_nonneg _))
  · intro n
    have htwo : 0 ≤ 2/a := div_nonneg (by norm_num) ha.le
    calc
      ‖x n‖ ≤ (2/a)*‖g (x n)‖ := C.point_bound (hstay n)
      _ ≤ (2/a)*(G*gamma^n*‖g (x 0)‖) := mul_le_mul_of_nonneg_left (hgrad n) htwo
      _ ≤ (2/a)*(G*gamma^n*((b+a/2)*‖x 0‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (C.norm_equivalence hx0).2
            (mul_nonneg hG.le (pow_nonneg hgamma.le n))) htwo
      _ = ((2/a)*G*(b+a/2))*gamma^n*‖x 0‖ := by ring
      _ ≤ K*gamma^n*‖x 0‖ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hgamma.le n)) (norm_nonneg _)

end BB.Local
