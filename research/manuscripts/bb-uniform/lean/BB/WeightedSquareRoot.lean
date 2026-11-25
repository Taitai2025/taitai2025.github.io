import BB.OperatorBounds

noncomputable section
namespace BB.Operator

open Module.End
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The positive spectral square root, built from the proved eigenspace decomposition. -/
def weightSqrt {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric) : E →ₗ[ℝ] E where
  toFun u := hW.diagonalization.symm
    (fun μ : Eigenvalues W => Real.sqrt (μ:ℝ) • hW.diagonalization u μ)
  map_add' u v := by
    apply hW.diagonalization.injective
    simp only [map_add,LinearIsometryEquiv.apply_symm_apply]
    ext μ
    simp only [PiLp.add_apply,smul_add]
  map_smul' t u := by
    apply hW.diagonalization.injective
    simp only [map_smul,LinearIsometryEquiv.apply_symm_apply]
    ext μ
    simp only [PiLp.smul_apply,smul_smul,RingHom.id_apply,mul_comm]

theorem weightSqrt_coordinates {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric) (u : E)
    (μ : Eigenvalues W) :
    hW.diagonalization (weightSqrt hW u) μ = Real.sqrt (μ:ℝ) • hW.diagonalization u μ := by
  exact congrArg (fun y => y μ) (hW.diagonalization.apply_symm_apply _)

theorem weightSqrt_commutes {H W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hcomm : Function.Commute H W) : Function.Commute H (weightSqrt hW) := by
  intro u
  apply hW.diagonalization.injective
  ext μ
  rw [diagonalization_commuting hW hcomm.symm,weightSqrt_coordinates,
    weightSqrt_coordinates,diagonalization_commuting hW hcomm.symm,map_smul]

/-- The square-root map realizes exactly the W inner product. -/
theorem weightSqrt_inner {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ) (u v : E) :
    ⟪weightSqrt hW u,weightSqrt hW v⟫_ℝ = ⟪u,W v⟫_ℝ := by
  rw [← hW.diagonalization.inner_map_map,← hW.diagonalization.inner_map_map u (W v),
    PiLp.inner_apply,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro μ _
  rw [weightSqrt_coordinates,weightSqrt_coordinates,hW.diagonalization_apply_self_apply,
    real_inner_smul_left,real_inner_smul_right,real_inner_smul_right]
  rw [← mul_assoc,← pow_two,Real.sq_sqrt (eigenvalue_pos hWpd μ).le]

theorem weightSqrt_sq_norm {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ) (u : E) :
    ‖weightSqrt hW u‖^2 = ⟪u,W u⟫_ℝ := by
  rw [← real_inner_self_eq_norm_sq,weightSqrt_inner hW hWpd]

theorem weightSqrt_ne_zero {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ) {u : E} (hu : u ≠ 0) :
    weightSqrt hW u ≠ 0 := by
  intro hz
  have hh := weightSqrt_sq_norm hW hWpd u
  rw [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0)] at hh
  have hp := hWpd u hu
  linarith only [hh,hp]

theorem weightSqrt_norm_bounds {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    {m χ : ℝ} (hm : 0 < m) (hχ : 0 ≤ χ)
    (hq : ∀ x : E, m*‖x‖^2 ≤ ⟪x,W x⟫_ℝ ∧ ⟪x,W x⟫_ℝ ≤ (χ*m)*‖x‖^2)
    (u : E) :
    Real.sqrt m*‖u‖ ≤ ‖weightSqrt hW u‖ ∧
    ‖weightSqrt hW u‖ ≤ (Real.sqrt χ*Real.sqrt m)*‖u‖ := by
  have hs := weightSqrt_sq_norm hW hWpd u
  have hms := Real.sq_sqrt hm.le
  have hχs := Real.sq_sqrt hχ
  constructor
  · have hsq : (Real.sqrt m*‖u‖)^2 ≤ ‖weightSqrt hW u‖^2 := by
      rw [mul_pow,hms,hs]
      exact (hq u).1
    nlinarith only [hsq,norm_nonneg (weightSqrt hW u),mul_nonneg (Real.sqrt_nonneg m) (norm_nonneg u)]
  · have hsq : ‖weightSqrt hW u‖^2 ≤ ((Real.sqrt χ*Real.sqrt m)*‖u‖)^2 := by
      rw [mul_pow,mul_pow,hms,hχs,hs]
      exact (hq u).2
    have hn := mul_nonneg (mul_nonneg (Real.sqrt_nonneg χ) (Real.sqrt_nonneg m)) (norm_nonneg u)
    nlinarith only [hsq,norm_nonneg (weightSqrt hW u),hn]

end BB.Operator
