import BB.ObjectiveGap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

noncomputable section
namespace BB.Local

open Set Metric InnerProductSpace
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- C² regularity makes the actual derivative of the actual gradient symmetric.
No symmetry assumption is supplied as extra operator data. -/
theorem c2_hessian_symmetric {f : E → ℝ} {R : ℝ}
    (hf : ContDiffOn ℝ 2 f (ball (0:E) R)) {x : E} (hx : ‖x‖ < R) :
    (fderiv ℝ (gradient f) x).toLinearMap.IsSymmetric := by
  let T : E →L[ℝ] (E →L[ℝ] ℝ) :=
    (toDual ℝ E).toContinuousLinearEquiv.toContinuousLinearMap
  have hmem : x ∈ ball (0:E) R := by simpa only [mem_ball,dist_zero_right] using hx
  have hg : HasFDerivAt (gradient f) (fderiv ℝ (gradient f) x) x :=
    (c2_gradient_derivatives hf hx).2
  have hsecond : HasFDerivAt (fun z => T (gradient f z))
      (T.comp (fderiv ℝ (gradient f) x)) x :=
    T.hasFDerivAt.comp x hg
  have hlocal : ∀ᶠ z in 𝓝 x, HasFDerivAt f (T (gradient f z)) z := by
    filter_upwards [isOpen_ball.mem_nhds hmem] with z hz
    have hzn : ‖z‖ < R := by simpa only [mem_ball,dist_zero_right] using hz
    exact (c2_gradient_derivatives hf hzn).1.hasFDerivAt
  intro v w
  have hs := second_derivative_symmetric_of_eventually hlocal hsecond v w
  change ⟪fderiv ℝ (gradient f) x v,w⟫_ℝ = ⟪fderiv ℝ (gradient f) x w,v⟫_ℝ at hs
  change ⟪fderiv ℝ (gradient f) x v,w⟫_ℝ = ⟪v,fderiv ℝ (gradient f) x w⟫_ℝ
  exact hs.trans (real_inner_comm _ _)

end BB.Local
