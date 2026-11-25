import BB.OperatorSharpness
import BB.SecantPerturbation

set_option autoImplicit false

noncomputable section
namespace BB.LocalSharpness
open BB.Operator BB.Secant Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem two_eigenvector_norm_sq {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≠ b) {u v : E} (hu : H u = a • u) (hv : H v = b • v) :
    ‖u+v‖^2 = ‖u‖^2+‖v‖^2 := by
  simpa only [pow_two] using
    norm_add_sq_eq_norm_sq_add_norm_sq_real (eigenvectors_inner_eq_zero hH hab hu hv)

theorem two_eigenvector_moment {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≠ b) {u v : E} (hu : H u = a • u) (hv : H v = b • v) :
    @inner ℝ _ _ (u+v) (H (u+v)) = a*‖u‖^2+b*‖v‖^2 := by
  have huv := eigenvectors_inner_eq_zero hH hab hu hv
  have hvu := eigenvectors_inner_eq_zero hH hab.symm hv hu
  rw [H.map_add,hu,hv,inner_add_left,inner_add_right,inner_add_right]
  simp only [inner_smul_right,huv,hvu,real_inner_self_eq_norm_sq,mul_zero,zero_add,add_zero]

theorem two_eigenvector_Hnorm_sq {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≠ b) {u v : E} (hu : H u = a • u) (hv : H v = b • v) :
    ‖H (u+v)‖^2 = a^2*‖u‖^2+b^2*‖v‖^2 := by
  have huv := eigenvectors_inner_eq_zero hH hab hu hv
  rw [H.map_add,hu,hv,norm_add_sq_real,real_inner_smul_left,inner_smul_right,huv]
  simp only [mul_zero,add_zero,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

/-- The midpoint is in the exact BB2--BB1 interval if and only if the two
endpoint energies satisfy the two stated inequalities. -/
theorem midpoint_interval_iff_energy {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : E}
    (hu : H u = a • u) (hv : H v = b • v) (hu0 : u ≠ 0) :
    (bb2 (u+v) (H (u+v)) ≤ 2/(a+b) ∧ 2/(a+b) ≤ bb1 (u+v) (H (u+v))) ↔
      (a*‖u‖^2 ≤ b*‖v‖^2 ∧ ‖v‖^2 ≤ ‖u‖^2) := by
  have hb : 0 < b := ha.trans hab
  have hA : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu0)
  have hB : 0 ≤ ‖v‖^2 := sq_nonneg _
  have hsum : 0 < a+b := add_pos ha hb
  have hD : 0 < a*‖u‖^2+b*‖v‖^2 :=
    add_pos_of_pos_of_nonneg (mul_pos ha hA) (mul_nonneg hb.le hB)
  have hD2 : 0 < a^2*‖u‖^2+b^2*‖v‖^2 :=
    add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos ha) hA) (mul_nonneg (sq_nonneg b) hB)
  rw [bb1,bb2,two_eigenvector_norm_sq hH hab.ne hu hv,
    two_eigenvector_moment hH hab.ne hu hv,two_eigenvector_Hnorm_sq hH hab.ne hu hv,
    div_le_div_iff hD2 hsum,div_le_div_iff hsum hD]
  constructor
  · rintro ⟨hlo,hhi⟩
    constructor
    · apply (mul_le_mul_left (sub_pos.mpr hab)).mp
      nlinarith only [hlo]
    · apply (mul_le_mul_left (sub_pos.mpr hab)).mp
      nlinarith only [hhi]
  · rintro ⟨hlo,hhi⟩
    have hlo' := mul_le_mul_of_nonneg_left hlo (sub_pos.mpr hab).le
    have hhi' := mul_le_mul_of_nonneg_left hhi (sub_pos.mpr hab).le
    constructor <;> nlinarith only [hlo',hhi']

/-- Exact endpoint-ratio criterion stated in the local sharpness paragraph. -/
theorem midpoint_interval_iff_ratio {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : E}
    (hu : H u = a • u) (hv : H v = b • v) (hu0 : u ≠ 0) :
    (bb2 (u+v) (H (u+v)) ≤ 2/(a+b) ∧ 2/(a+b) ≤ bb1 (u+v) (H (u+v))) ↔
      (a/b ≤ ‖v‖^2/‖u‖^2 ∧ ‖v‖^2/‖u‖^2 ≤ 1) := by
  have hb := ha.trans hab
  have hA := sq_pos_of_pos (norm_pos_iff.mpr hu0)
  rw [midpoint_interval_iff_energy hH ha hab hu hv hu0,
    div_le_div_iff hb hA,div_le_one hA]
  constructor <;> rintro ⟨hlo,hhi⟩ <;> constructor <;> nlinarith only [hlo,hhi]

/-- An explicit positive first step works for every prescribed startup cap. -/
theorem exists_small_first_step {a b A₀ : ℝ} (ha : 0 < a) (hab : a < b) (hA₀ : 0 < A₀) :
    ∃ t : ℝ, 0 < t ∧ t ≤ A₀ ∧ t < 1/b ∧
      a*(1-t*a)^2 ≤ b*(1-t*b)^2 ∧ (1-t*b)^2 ≤ (1-t*a)^2 := by
  have hb := ha.trans hab
  have hsum : 0 < a+b := add_pos ha hb
  let t := min A₀ (1/(2*(a+b)))
  have ht : 0 < t := lt_min hA₀ (one_div_pos.mpr (mul_pos (by norm_num) hsum))
  have hcap : t ≤ 1/(2*(a+b)) := min_le_right _ _
  have htb : t < 1/b := hcap.trans_lt
    (one_div_lt_one_div_of_lt hb (by linarith only [ha,hb]))
  have htb' : t*b < 1 := (lt_div_iff hb).mp htb
  have hta : t*a < 1 := (mul_lt_mul_of_pos_left hab ht).trans htb'
  have hcoeff : 1-t*b ≤ 1-t*a := by nlinarith only [mul_le_mul_of_nonneg_left hab.le ht.le]
  have hlin : 0 ≤ 1-2*t*(a+b) := by
    have hh := (le_div_iff (mul_pos (by norm_num : (0 : ℝ) < 2) hsum)).mp hcap
    nlinarith only [hh]
  have hsq : 0 ≤ t^2*(a^2+a*b+b^2) := by positivity
  have hprod := mul_nonneg (sub_pos.mpr hab).le (add_nonneg hlin hsq)
  refine ⟨t,ht,min_le_left _ _,htb,?_,?_⟩
  · nlinarith only [hprod]
  · nlinarith only [hta,htb',hcoeff]

theorem exists_small_first_step_ratio {a b A₀ : ℝ} (ha : 0 < a) (hab : a < b) (hA₀ : 0 < A₀) :
    ∃ t : ℝ, 0 < t ∧ t ≤ A₀ ∧ t < 1/b ∧
      a/b ≤ ((1-t*b)/(1-t*a))^2 ∧ ((1-t*b)/(1-t*a))^2 ≤ 1 := by
  obtain ⟨t,ht,hcap,htb,hlo,hhi⟩ := exists_small_first_step ha hab hA₀
  have hb := ha.trans hab
  have hta : t*a < 1 := (mul_lt_mul_of_pos_left hab ht).trans ((lt_div_iff hb).mp htb)
  have hden : 0 < (1-t*a)^2 := sq_pos_of_pos (sub_pos.mpr hta)
  refine ⟨t,ht,hcap,htb,?_,?_⟩
  · rw [div_pow]
    apply (div_le_div_iff hb hden).mpr
    nlinarith only [hlo]
  · rw [div_pow]
    exact (div_le_one hden).mpr hhi

end BB.LocalSharpness
