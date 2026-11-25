import BB.QuadraticObjective
import BB.OperatorBounds

/-! # The literal affine quadratic model from the manuscript

The linear term is arbitrary. The gradient and Hessian are genuine derivatives,
and the minimizer is obtained from finite-dimensional positive definiteness.
-/

noncomputable section
namespace BB.Quadratic

open InnerProductSpace Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def affineObjective (H : E →L[ℝ] E) (d x : E) : ℝ :=
  (1/2:ℝ)*⟪x,H x⟫_ℝ-⟪d,x⟫_ℝ

theorem affineObjective_contDiff (H : E →L[ℝ] E) (d : E) (n : ℕ∞) :
    ContDiff ℝ n (affineObjective H d) :=
  (objective_contDiff H n).sub (toDual ℝ E d).contDiff

theorem affineObjective_hasGradientAt (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (d x : E) :
    HasGradientAt (affineObjective H d) (H x-d) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hh := (objective_hasGradientAt H hH x).hasFDerivAt.sub (toDual ℝ E d).hasFDerivAt
  simpa only [map_sub,affineObjective,objective,toDual_apply] using hh

theorem affineObjective_gradient (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (d : E) :
    gradient (affineObjective H d) = fun x => H x-d :=
  gradient_eq (affineObjective_hasGradientAt H hH d)

theorem affineObjective_hessian (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric) (d x : E) :
    fderiv ℝ (gradient (affineObjective H d)) x = H := by
  rw [affineObjective_gradient H hH]
  exact (H.hasFDerivAt.sub_const d).fderiv

/-- Completing the square uses the true solution Hp=d and self-adjointness. -/
theorem affineObjective_gap (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {d p : E} (hp : H p=d) (x : E) :
    affineObjective H d x-affineObjective H d p=objective H (x-p) := by
  subst d
  have hcross : ⟪p,H x⟫_ℝ=⟪x,H p⟫_ℝ :=
    (hH p x).symm.trans (real_inner_comm _ _)
  simp only [affineObjective,objective,map_sub,inner_sub_left,inner_sub_right,
    real_inner_comm (H p) x,real_inner_comm (H p) p,hcross]
  ring

theorem affineObjective_gradient_error (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {d p : E} (hp : H p=d) (x : E) :
    gradient (affineObjective H d) x=H (x-p) := by
  rw [affineObjective_gradient H hH,map_sub,hp]

/-- The actual affine-quadratic gradient satisfies the exact linear BB recurrence. -/
theorem affineObjective_gradient_step (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (d x : E) (α : ℝ) :
    gradient (affineObjective H d) (x-α • gradient (affineObjective H d) x) =
      gradient (affineObjective H d) x-α • H (gradient (affineObjective H d) x) := by
  rw [affineObjective_gradient H hH]
  simp only [map_sub,map_smul]
  abel

theorem positiveDefinite_injective (H : E →L[ℝ] E)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) : Function.Injective H := by
  intro x y hxy
  apply sub_eq_zero.mp
  by_contra hne
  have hh := hpd (x-y) hne
  have hzero : H (x-y)=0 := by rw [map_sub,hxy,sub_self]
  rw [hzero,inner_zero_right] at hh
  exact lt_irrefl _ hh

theorem affineObjective_strict_min (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) {d p : E} (hp : H p=d)
    {x : E} (hxp : x ≠ p) : affineObjective H d p < affineObjective H d x := by
  have hg := objective_pos H hpd (sub_ne_zero.mpr hxp)
  rw [← affineObjective_gap H hH hp x] at hg
  exact sub_pos.mp hg

theorem affineObjective_minimal (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) {d p : E} (hp : H p=d) (x : E) :
    affineObjective H d p ≤ affineObjective H d x := by
  by_cases hx : x=p
  · rw [hx]
  · exact (affineObjective_strict_min H hH hpd hp hx).le

section FiniteDimensional
variable [FiniteDimensional ℝ E]

/-- Finite-dimensional SPD operators are genuine linear equivalences. -/
def hessianEquiv (H : E →L[ℝ] E)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) : E ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective H.toLinearMap
    ⟨positiveDefinite_injective H hpd,
      LinearMap.surjective_of_injective (positiveDefinite_injective H hpd)⟩

/-- This is H^{-1}d, with the inverse supplied by proved invertibility. -/
def affineMinimizer (H : E →L[ℝ] E)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) (d : E) : E :=
  (hessianEquiv H hpd).symm d

theorem affineMinimizer_eq (H : E →L[ℝ] E)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) (d : E) :
    H (affineMinimizer H hpd d)=d :=
  (hessianEquiv H hpd).apply_symm_apply d

theorem exists_unique_linear_solution (H : E →L[ℝ] E)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) (d : E) :
    ∃! p : E, H p=d := by
  refine ⟨affineMinimizer H hpd d,affineMinimizer_eq H hpd d,?_⟩
  intro y hy
  exact positiveDefinite_injective H hpd (hy.trans (affineMinimizer_eq H hpd d).symm)

theorem exists_unique_affine_minimizer (H : E →L[ℝ] E)
    (hH : H.toLinearMap.IsSymmetric)
    (hpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ) (d : E) :
    ∃! p : E, ∀ x : E, affineObjective H d p ≤ affineObjective H d x := by
  let p := affineMinimizer H hpd d
  have hp : H p=d := affineMinimizer_eq H hpd d
  refine ⟨p,affineObjective_minimal H hH hpd hp,?_⟩
  intro q hq
  by_contra hne
  exact (not_lt_of_ge (hq p)) (affineObjective_strict_min H hH hpd hp hne)

/-- The operator-gradient/error comparison for the actual affine objective. -/
theorem affine_gradient_error_bounds (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H.toLinearMap, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    {d p : E} (hp : H p=d) (x : E) :
    a*‖x-p‖ ≤ ‖gradient (affineObjective H d) x‖ ∧
      ‖gradient (affineObjective H d) x‖ ≤ b*‖x-p‖ := by
  rw [affineObjective_gradient_error H hH hp]
  have hQ := BB.Operator.quadratic_bounds_of_spectral_bounds hH hspec
  exact ⟨BB.Operator.hessian_norm_lower ha.le (fun y => (hQ y).1) (x-p),
    (BB.Operator.positive_spectral_bounds hH ha hab hspec (x-p)).2⟩

/-- The original objective gap has the manuscript's exact gradient comparisons. -/
theorem affine_actual_gap_bounds (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H.toLinearMap, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    {d p : E} (hp : H p=d) (x : E) :
    (1/(2*b))*‖gradient (affineObjective H d) x‖^2 ≤ affineObjective H d x-affineObjective H d p ∧
      affineObjective H d x-affineObjective H d p ≤ (1/(2*a))*‖gradient (affineObjective H d) x‖^2 := by
  rw [affineObjective_gap H hH hp,affineObjective_gradient_error H hH hp]
  exact objective_gap_of_spectral_bounds H hH ha hab hspec (x-p)

theorem affine_distance_gap_bounds (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b : ℝ}
    (hspec : ∀ μ : Eigenvalues H.toLinearMap, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    {d p : E} (hp : H p=d) (x : E) :
    (a/2)*‖x-p‖^2 ≤ affineObjective H d x-affineObjective H d p ∧
      affineObjective H d x-affineObjective H d p ≤ (b/2)*‖x-p‖^2 := by
  rw [affineObjective_gap H hH hp]
  have hh := BB.Operator.quadratic_bounds_of_spectral_bounds hH hspec (x-p)
  change a*‖x-p‖^2 ≤ ⟪x-p,H (x-p)⟫_ℝ ∧
    ⟪x-p,H (x-p)⟫_ℝ ≤ b*‖x-p‖^2 at hh
  unfold objective
  constructor <;> nlinarith only [hh.1,hh.2]

end FiniteDimensional
end BB.Quadratic
