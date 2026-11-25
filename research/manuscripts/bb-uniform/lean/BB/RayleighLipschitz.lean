import BB.OperatorBounds
import BB.SecantPerturbation

noncomputable section
namespace BB.Operator

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def unitVector (x : E) : E := ‖x‖⁻¹ • x

theorem unitVector_norm {x : E} (hx : x ≠ 0) : ‖unitVector x‖ = 1 := by
  unfold unitVector
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact inv_mul_cancel (norm_ne_zero_iff.mpr hx)

theorem unitVector_sub_bound_ordered {x y : E} (hx : x ≠ 0) (hy : y ≠ 0)
    (hyx : ‖y‖ ≤ ‖x‖) :
    ‖unitVector x-unitVector y‖ ≤ 2*‖x-y‖/‖x‖ := by
  have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hny : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hinv : ‖x‖⁻¹ ≤ ‖y‖⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hny hyx
  have hid : unitVector x-unitVector y =
      ‖x‖⁻¹ • (x-y)+(‖x‖⁻¹-‖y‖⁻¹) • y := by
    unfold unitVector
    rw [smul_sub,sub_smul]
    abel
  rw [hid]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖+‖(‖x‖⁻¹-‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹*‖x-y‖+(‖y‖⁻¹-‖x‖⁻¹)*‖y‖ := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hnx),abs_of_nonpos (sub_nonpos.mpr hinv)]
      ring
    _ = (‖x-y‖+(‖x‖-‖y‖))/‖x‖ := by
      field_simp
      <;> ring
    _ ≤ 2*‖x-y‖/‖x‖ := by
      apply (div_le_div_right hnx).2
      linarith only [norm_sub_norm_le x y]

/-- Normalization costs at most twice the distance divided by the larger norm. -/
theorem unitVector_sub_bound {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    ‖unitVector x-unitVector y‖ ≤ 2*‖x-y‖/max ‖x‖ ‖y‖ := by
  rcases le_total ‖y‖ ‖x‖ with h|h
  · rw [max_eq_left h]
    exact unitVector_sub_bound_ordered hx hy h
  · rw [max_eq_right h,norm_sub_rev (unitVector x) (unitVector y),norm_sub_rev x y]
    exact unitVector_sub_bound_ordered hy hx h

variable [FiniteDimensional ℝ E]

/-- Centering at the midpoint gives the exact half-width operator norm bound. -/
theorem midpoint_shift_norm_bound {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b) (v : E) :
    ‖H v-((a+b)/2) • v‖ ≤ ((b-a)/2)*‖v‖ := by
  apply coordinate_multiplier_norm_bound hH (fun μ => (μ:ℝ)-(a+b)/2)
    (by linarith only [hab]) ?_ ?_
  · intro μ
    unfold coordinates
    rw [map_sub,map_smul]
    change hH.diagonalization (H v) μ-((a+b)/2) • hH.diagonalization v μ = _
    rw [hH.diagonalization_apply_self_apply,sub_smul]
  · intro μ
    change |(μ:ℝ)-(a+b)/2| ≤ (b-a)/2
    apply abs_le.mpr
    constructor <;> linarith only [(hspec μ).1,(hspec μ).2]

/-- The Rayleigh quadratic form has Lipschitz constant b-a on the unit sphere. -/
theorem unit_rayleigh_lipschitz {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    {x y : E} (hx : ‖x‖=1) (hy : ‖y‖=1) :
    |⟪x,H x⟫_ℝ-⟪y,H y⟫_ℝ| ≤ (b-a)*‖x-y‖ := by
  let D : E →ₗ[ℝ] E := H-((a+b)/2) • LinearMap.id
  have hD (z : E) : ‖D z‖ ≤ ((b-a)/2)*‖z‖ := by
    exact midpoint_shift_norm_bound hH hab hspec z
  have hid : ⟪x,H x⟫_ℝ-⟪y,H y⟫_ℝ = ⟪x-y,D x⟫_ℝ+⟪y,D (x-y)⟫_ℝ := by
    simp only [D,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.id_apply,map_sub,
      inner_sub_left,inner_sub_right,real_inner_smul_right,real_inner_self_eq_norm_sq,hx,hy]
    ring
  rw [hid]
  calc
    _ ≤ |⟪x-y,D x⟫_ℝ|+|⟪y,D (x-y)⟫_ℝ| := abs_add _ _
    _ ≤ ‖x-y‖*‖D x‖+‖y‖*‖D (x-y)‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ ‖x-y‖*(((b-a)/2)*‖x‖)+‖y‖*(((b-a)/2)*‖x-y‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (hD x) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (hD (x-y)) (norm_nonneg _))
    _ = (b-a)*‖x-y‖ := by rw [hx,hy]; ring

theorem bb1_unitVector (H : E →ₗ[ℝ] E) {x : E} (hx : x ≠ 0) :
    BB.Secant.bb1 (unitVector x) (H (unitVector x))=BB.Secant.bb1 x (H x) := by
  unfold unitVector
  rw [map_smul]
  exact BB.Secant.bb1_smul x (H x) (inv_ne_zero (norm_ne_zero_iff.mpr hx))

/-- Reciprocal Rayleigh quotients on normalized directions, with the exact a^-2 factor. -/
theorem reciprocal_rayleigh_unit_bound {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    |BB.Secant.bb1 x (H x)-BB.Secant.bb1 y (H y)| ≤
      ((b-a)/a^2)*‖unitVector x-unitVector y‖ := by
  let X := unitVector x
  let Y := unitVector y
  have hnX : ‖X‖=1 := unitVector_norm hx
  have hnY : ‖Y‖=1 := unitVector_norm hy
  have hX : a ≤ ⟪X,H X⟫_ℝ := by
    simpa only [hnX,one_pow,mul_one] using (quadratic_bounds_of_spectral_bounds hH hspec X).1
  have hY : a ≤ ⟪Y,H Y⟫_ℝ := by
    simpa only [hnY,one_pow,mul_one] using (quadratic_bounds_of_spectral_bounds hH hspec Y).1
  have hXp := ha.trans_le hX
  have hYp := ha.trans_le hY
  have hdiff := unit_rayleigh_lipschitz hH hab hspec hnX hnY
  have hden : a^2 ≤ ⟪X,H X⟫_ℝ*⟪Y,H Y⟫_ℝ := by
    have hh := mul_le_mul hX hY ha.le hXp.le
    nlinarith only [hh]
  rw [← bb1_unitVector H hx,← bb1_unitVector H hy]
  change |‖X‖^2/⟪X,H X⟫_ℝ-‖Y‖^2/⟪Y,H Y⟫_ℝ| ≤ _
  rw [hnX,hnY,one_pow,one_div,one_div,inv_sub_inv hXp.ne' hYp.ne',
    abs_div,abs_mul,abs_of_pos hXp,abs_of_pos hYp,abs_sub_comm]
  calc
    _ ≤ ((b-a)*‖X-Y‖)/a^2 := div_le_div
      (mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg _)) hdiff (sq_pos_of_pos ha) hden
    _ = ((b-a)/a^2)*‖unitVector x-unitVector y‖ := by ring

end BB.Operator
