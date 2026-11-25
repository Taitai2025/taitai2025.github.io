import BB.NonlinearMain

/-! # Translation back to an arbitrary stationary point -/

set_option autoImplicit false
noncomputable section
namespace BB.Local

open Set Metric MeasureTheory Filter Module.End BB.Operator
open scoped Topology

section Derivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Translation preserves the total derivative, including nondifferentiable points. -/
theorem fderiv_translate (f : E → F) (p y : E) :
    fderiv ℝ (fun z => f (p+z)) y = fderiv ℝ f (p+y) := by
  by_cases hf : DifferentiableAt ℝ f (p+y)
  · have hh := hf.hasFDerivAt.comp y ((hasFDerivAt_id y).const_add p)
    simpa only [Function.comp_def,ContinuousLinearMap.comp_id] using hh.fderiv
  · have hg : ¬ DifferentiableAt ℝ (fun z => f (p+z)) y := by
      intro hh
      have hp : p+y-p = y := by abel
      have hh' : DifferentiableAt ℝ (fun z => f (p+z)) (p+y-p) := by simpa only [hp] using hh
      have hcomp := hh'.comp (p+y) ((differentiableAt_id).sub_const p)
      apply hf
      convert hcomp using 1
      funext z
      change f z = f (p+(z-p))
      congr 1
      abel
    rw [fderiv_zero_of_not_differentiableAt hg,fderiv_zero_of_not_differentiableAt hf]

end Derivative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem sortedLambda_congr {A B : E →ₗ[ℝ] E} (h : A = B) {n : ℕ}
    (hA : Fintype.card (Eigenvalues A) = n) (hB : Fintype.card (Eigenvalues B) = n) :
    sortedLambda A hA = sortedLambda B hB := by
  subst B
  rfl

/-- The actual gradient obeys translation at every point. -/
theorem gradient_translate (f : E → ℝ) (p y : E) :
    gradient (fun z => f (p+z)) y = gradient f (p+y) := by
  unfold gradient
  rw [fderiv_translate]

/-- Consequently the actual Hessian obeys the same translation law. -/
theorem hessian_translate (f : E → ℝ) (p y : E) :
    hessian (fun z => f (p+z)) y = hessian f (p+y) := by
  have hg : gradient (fun z => f (p+z)) = fun y => gradient f (p+y) :=
    funext (gradient_translate f p)
  unfold hessian
  rw [hg,fderiv_translate]

theorem c2_translate {f : E → ℝ} {p : E} {r : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball p r)) :
    ContDiffOn ℝ 2 (fun y => f (p+y)) (ball (0:E) r) := by
  apply hf.comp (contDiff_const.add contDiff_id).contDiffOn
  intro y hy
  simpa only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero] using hy

theorem intervalChoice_translate (f : E → ℝ) (p x y : E) (alpha : ℝ) :
    intervalChoice (gradient (fun z => f (p+z))) (x-p) (y-p) alpha ↔
      intervalChoice (gradient f) x y alpha := by
  have hx : p+(x-p) = x := by abel
  have hy : p+(y-p) = y := by abel
  have hsub : (y-p)-(x-p) = y-x := by abel
  simp only [intervalChoice,gradient_translate,hx,hy,hsub]

/-- Theorem 5.1 in the original coordinates, with any stationary point x*. -/
theorem theorem_5_1_at (f : E → ℝ) (p : E) {r A₀ : ℝ} (hr : 0 < r) (hA₀ : 0 < A₀)
    (hf : ContDiffOn ℝ 2 f (ball p r))
    (hstationary : gradient f p = 0)
    (hH : (hessian f p).toLinearMap.IsSymmetric)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (hessian f p x))
    {n : ℕ} (hn : Fintype.card (Eigenvalues (hessian f p).toLinearMap) = n+2)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hlim : Tendsto omega (nhdsWithin (0:ℝ) (Ioi 0)) (𝓝 0))
    (hmodulus : ∀ x : E, ‖x-p‖ < r → ‖hessian f x-hessian f p‖ ≤ omega ‖x-p‖)
    (hDini : IntervalIntegrable (fun t => omega t/t) volume 0 r) :
    let c := BB.endpointRate (sortedLambda (hessian f p).toLinearMap hn 0)
      (sortedLambda (hessian f p).toLinearMap hn (Fin.last (n+1)))
    ∃ delta K : ℝ, 0 < delta ∧ 0 < K ∧
      ∀ (x : ℕ → E) (alpha : ℕ → ℝ), ‖x 0-p‖ < delta →
        (∀ n, 0 < alpha n) → alpha 0 ≤ A₀ →
        (∀ n, x (n+1)=x n-alpha n • gradient f (x n)) →
        (∀ n, intervalChoice (gradient f) (x n) (x (n+1)) (alpha (n+1))) →
        (∀ n, ‖x n-p‖ < r) ∧
        (∀ n, gradient f (x n) ≠ 0 →
          0 < @inner ℝ _ _ (x (n+1)-x n) (gradient f (x (n+1))-gradient f (x n)) ∧
          0 < ‖gradient f (x (n+1))-gradient f (x n)‖^2) ∧
        (∀ n, ‖gradient f (x n)‖ ≤ K*c^n*‖gradient f (x 0)‖) ∧
        (∀ n, ‖x n-p‖ ≤ K*c^n*‖x 0-p‖) ∧
        (∀ n, f (x n)-f p ≤ K*c^(2*n)*(f (x 0)-f p)) := by
  let F : E → ℝ := fun y => f (p+y)
  have hHF : hessian F 0 = hessian f p := by
    simpa only [add_zero,F] using hessian_translate f p 0
  have hnF : Fintype.card (Eigenvalues (hessian F 0).toLinearMap) = n+2 := by
    rw [hHF]
    exact hn
  have hsymF : (hessian F 0).toLinearMap.IsSymmetric := by rwa [hHF]
  have hpdF : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (hessian F 0 x) := by rwa [hHF]
  have hzF : gradient F 0 = 0 := by simpa only [F,gradient_translate,add_zero] using hstationary
  have hmodF : ∀ y : E, ‖y‖ < r → ‖hessian F y-hessian F 0‖ ≤ omega ‖y‖ := by
    intro y hy
    simpa only [F,hessian_translate,add_zero,add_sub_cancel_left] using hmodulus (p+y)
      (by simpa only [add_sub_cancel_left] using hy)
  have hmain := theorem_5_1 F hr hA₀ (c2_translate hf) hzF hsymF hpdF hnF
    omega hmono hnonneg hlim hmodF hDini
  have hlam := sortedLambda_congr (congrArg ContinuousLinearMap.toLinearMap hHF) hnF hn
  dsimp only at hmain
  rw [hlam] at hmain
  obtain ⟨delta,K,hdelta,hK,huniform⟩ := hmain
  refine ⟨delta,K,hdelta,hK,?_⟩
  intro x alpha hx halpha hA hstep hchoice
  let y : ℕ → E := fun j => x j-p
  have hg (j : ℕ) : gradient F (y j) = gradient f (x j) := by
    dsimp only [F]
    rw [gradient_translate]
    congr 1
    dsimp [y]
    abel
  have hrec : ∀ j, y (j+1) = y j-alpha j • gradient F (y j) := by
    intro j
    rw [hg]
    dsimp [y]
    rw [hstep j]
    abel
  have hch : ∀ j, intervalChoice (gradient F) (y j) (y (j+1)) (alpha (j+1)) := by
    intro j
    exact (intervalChoice_translate f p (x j) (x (j+1)) (alpha (j+1))).mpr (hchoice j)
  obtain ⟨hstay,hden,hgrad,herror,hgap⟩ := huniform y alpha hx halpha hA hrec hch
  refine ⟨hstay,?_,?_,herror,?_⟩
  · intro j hj
    have hh := hden j (by rwa [hg])
    have hsub : y (j+1)-y j = x (j+1)-x j := by dsimp [y]; abel
    simpa only [hg,hsub] using hh
  · intro j
    simpa only [hg] using hgrad j
  · intro j
    have hFy (i : ℕ) : F (y i) = f (x i) := by
      dsimp [F,y]
      congr 1
      abel
    have hF0 : F 0 = f p := by simp only [F,add_zero]
    simpa only [hFy,hF0] using hgap j

end BB.Local
