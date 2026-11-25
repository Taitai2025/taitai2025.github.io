import BB.NonlinearMain
import BB.NonlinearRoughRates
import BB.IntervalTheorem
import BB.ObjectiveGap

/-!
# Local C² rates at every larger factor, without a Dini assumption

The Hessian here is the genuine Fréchet derivative of the genuine gradient.
The neighborhood and comparison constant precede every initial point, first
stepsize, and sequence of secant choices in the theorem's quantifiers.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Local

open Set Metric MeasureTheory Filter Module.End BB.Operator
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Fully instantiated local gradient theorem. No Lyapunov certificate or
perturbation recurrence is an assumption. -/
theorem GradientControl.uniform_spectral_rough_rate
    {g : E → E} {D : E → E →L[ℝ] E} {H : E →L[ℝ] E}
    {n : ℕ} (hn : Fintype.card (Eigenvalues H.toLinearMap) = n+2)
    (hH : H.toLinearMap.IsSymmetric)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {R : ℝ} {omega : ℝ → ℝ}
    (C : GradientControl g D H (sortedLambda H.toLinearMap hn 0)
      (sortedLambda H.toLinearMap hn (Fin.last (n+1))) R omega)
    {A₀ : ℝ} (hA₀ : 0 < A₀)
    (hlim : Tendsto omega (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 0))
    {gamma : ℝ}
    (hcg : BB.endpointRate (sortedLambda H.toLinearMap hn 0)
      (sortedLambda H.toLinearMap hn (Fin.last (n+1))) < gamma)
    (hg1 : gamma < 1) :
    ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧
      ∀ (x : ℕ → E) (alpha : ℕ → ℝ), ‖x 0‖ < delta →
        (∀ n, 0 < alpha n) → alpha 0 ≤ A₀ →
        (∀ n, x (n+1)=x n-alpha n • g (x n)) →
        (∀ n, intervalChoice g (x n) (x (n+1)) (alpha (n+1))) →
        (∀ n, ‖x n‖ < R) ∧
        (∀ n, g (x n) ≠ 0 →
          0 < @inner ℝ _ _ (x (n+1)-x n) (g (x (n+1))-g (x n)) ∧
          0 < ‖g (x (n+1))-g (x n)‖^2) ∧
        (∀ n, ‖g (x n)‖ ≤ K*gamma^n*‖g (x 0)‖) ∧
        (∀ n, ‖x n‖ ≤ K*gamma^n*‖x 0‖) := by
  let a := sortedLambda H.toLinearMap hn 0
  let b := sortedLambda H.toLinearMap hn (Fin.last (n+1))
  have hab : a < b := (sortedLambda_strictMono H.toLinearMap hn) (by
    change 0 < n+1
    omega)
  let M := max (1+(b+a/2)*A₀) (1+(b+a/2)*(2/a))
  have hM0 : 0 ≤ M := by
    have ha : 0 < a := C.a_pos
    have hb : 0 < b := ha.trans hab
    exact (show 0 ≤ 1+(b+a/2)*A₀ by positivity).trans (le_max_left _ _)
  obtain ⟨V⟩ := frozen_interval_certificate H hH hn hpd hM0
  exact C.uniform_rough_rate_of_certificate V (BB.endpointRate_pos C.a_pos hab)
    hcg hg1 hA₀ (le_max_left _ _) (le_max_right _ _) hlim

/-- Theorem 5.1, centered at the stationary point. Every derivative, secant,
gradient, error and objective-gap conclusion is tied to the same C² objective. -/
theorem theorem_5_1_without_dini (f : E → ℝ) {r A₀ : ℝ} (hr : 0 < r) (hA₀ : 0 < A₀)
    (hf : ContDiffOn ℝ 2 f (ball (0:E) r))
    (hstationary : gradient f 0 = 0)
    (hH : (hessian f 0).toLinearMap.IsSymmetric)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (hessian f 0 x))
    {n : ℕ} (hn : Fintype.card (Eigenvalues (hessian f 0).toLinearMap) = n+2)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hlim : Tendsto omega (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 0))
    (hmodulus : ∀ x : E, ‖x‖ < r → ‖hessian f x-hessian f 0‖ ≤ omega ‖x‖)
    {gamma : ℝ}
    (hcg : BB.endpointRate (sortedLambda (hessian f 0).toLinearMap hn 0)
      (sortedLambda (hessian f 0).toLinearMap hn (Fin.last (n+1))) < gamma)
    (hg1 : gamma < 1) :
    ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧
      ∀ (x : ℕ → E) (alpha : ℕ → ℝ), ‖x 0‖ < delta →
        (∀ n, 0 < alpha n) → alpha 0 ≤ A₀ →
        (∀ n, x (n+1)=x n-alpha n • gradient f (x n)) →
        (∀ n, intervalChoice (gradient f) (x n) (x (n+1)) (alpha (n+1))) →
        (∀ n, ‖x n‖ < r) ∧
        (∀ n, gradient f (x n) ≠ 0 →
          0 < @inner ℝ _ _ (x (n+1)-x n) (gradient f (x (n+1))-gradient f (x n)) ∧
          0 < ‖gradient f (x (n+1))-gradient f (x n)‖^2) ∧
        (∀ n, ‖gradient f (x n)‖ ≤ K*gamma^n*‖gradient f (x 0)‖) ∧
        (∀ n, ‖x n‖ ≤ K*gamma^n*‖x 0‖) ∧
        (∀ n, f (x n)-f 0 ≤ K*gamma^(2*n)*(f (x 0)-f 0)) := by
  let H := hessian f 0
  let a := sortedLambda H.toLinearMap hn 0
  let b := sortedLambda H.toLinearMap hn (Fin.last (n+1))
  have ha : 0 < a := sortedLambda_pos hn hpd 0
  have hab : a < b := (sortedLambda_strictMono H.toLinearMap hn) (by
    change 0 < n+1
    omega)
  have hb : 0 < b := ha.trans hab
  have hspec := sorted_spectral_bounds H.toLinearMap hn
  have hQ := quadratic_bounds_of_spectral_bounds hH hspec
  have hnorm : ‖H‖ ≤ b := by
    apply ContinuousLinearMap.opNorm_le_bound H hb.le
    exact fun v => (positive_spectral_bounds hH ha hab.le hspec v).2
  obtain ⟨R,hR,hRr,hsmall⟩ := BB.RadiusChoice.exists_coercivity_radius omega hlim ha hr
  have C : GradientControl (gradient f) (hessian f) H a b R omega := {
    a_pos := ha
    a_le_b := hab.le
    radius_pos := hR
    zero := hstationary
    derivative := fun x hx => (c2_gradient_derivatives hf (hx.trans hRr)).2
    modulus := fun x hx => hmodulus x (hx.trans hRr)
    coercive := fun x => (hQ x).1
    operator_bound := hnorm
    monotone := hmono
    nonnegative := hnonneg
    small := hsmall }
  have hgradf : ∀ x, ‖x‖ < R → HasGradientAt f (gradient f x) x :=
    fun x hx => (c2_gradient_derivatives hf (hx.trans hRr)).1
  obtain ⟨delta,K₀,hdelta,hK₀,huniform⟩ :=
    C.uniform_spectral_rough_rate hn hH hpd hA₀ hlim hcg hg1
  let J := (((b+a/2)/2)*K₀^2)/(a/4)
  let K := max K₀ J
  have hK : 0 < K := hK₀.trans_le (le_max_left _ _)
  have hc : 0 ≤ gamma := ((BB.endpointRate_pos ha hab).trans hcg).le
  refine ⟨delta,K,hdelta,hK,?_⟩
  intro x alpha hx halpha hA hstep hchoice
  obtain ⟨hstay,hden,hgrad,herror⟩ := huniform x alpha hx halpha hA hstep hchoice
  refine ⟨fun j => (hstay j).trans hRr,hden,?_,?_,?_⟩
  · intro j
    exact (hgrad j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K₀ J) (pow_nonneg hc j)) (norm_nonneg _))
  · intro j
    exact (herror j).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K₀ J) (pow_nonneg hc j)) (norm_nonneg _))
  · intro j
    have hgaps := fun k => C.objective_gap hgradf (hstay k)
    have hg := objective_rate_from_error (m := a/4) (L := (b+a/2)/2)
      (by positivity) (by positivity) hK₀.le hc (hgaps 0).1 (fun k => (hgaps k).2) herror j
    have hgap0 : 0 ≤ f (x 0)-f 0 :=
      (mul_nonneg (by positivity : 0 ≤ a/4) (sq_nonneg _)).trans (hgaps 0).1
    exact hg.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right K₀ J) (pow_nonneg hc (2*j))) hgap0)

end BB.Local
