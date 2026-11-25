import BB.OperatorCondition
import BB.SecantPerturbation

noncomputable section
namespace BB.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The affine commuting weight realizing one frozen BB1--BB2 interval choice. -/
def rawIntervalWeight (H : E →ₗ[ℝ] E) (η : ℝ) (u : E) : E →ₗ[ℝ] E :=
  (η*‖H u‖^2) • LinearMap.id + ((1-η)*⟪u,H u⟫_ℝ) • H

def rawIntervalScale (H : E →ₗ[ℝ] E) (a η : ℝ) (u : E) : ℝ :=
  η*‖H u‖^2 + (1-η)*⟪u,H u⟫_ℝ*a

/-- The zero-gradient branch uses the identity weight. Both quotient conventions are zero. -/
def intervalWeight (H : E →ₗ[ℝ] E) (η : ℝ) (u : E) : E →ₗ[ℝ] E := by
  classical
  exact if u=0 then LinearMap.id else rawIntervalWeight H η u

def intervalScale (H : E →ₗ[ℝ] E) (a η : ℝ) (u : E) : ℝ := by
  classical
  exact if u=0 then 1 else rawIntervalScale H a η u

theorem rawIntervalWeight_symmetric {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (η : ℝ) (u : E) : (rawIntervalWeight H η u).IsSymmetric := by
  intro x y
  simp only [rawIntervalWeight,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
    inner_add_left,inner_add_right,real_inner_smul_left,real_inner_smul_right,hH x y]

theorem rawIntervalWeight_commutes (H : E →ₗ[ℝ] E) (η : ℝ) (u : E) :
    Function.Commute H (rawIntervalWeight H η u) := by
  intro x
  simp only [rawIntervalWeight,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
    map_add,map_smul]

theorem intervalWeight_symmetric {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (η : ℝ) (u : E) : (intervalWeight H η u).IsSymmetric := by
  unfold intervalWeight
  split_ifs
  · exact LinearMap.isSymmetric_id
  · exact rawIntervalWeight_symmetric hH η u

theorem intervalWeight_commutes (H : E →ₗ[ℝ] E) (η : ℝ) (u : E) :
    Function.Commute H (intervalWeight H η u) := by
  unfold intervalWeight
  split_ifs
  · intro x; rfl
  · exact rawIntervalWeight_commutes H η u

theorem frozen_moments_pos {H : E →ₗ[ℝ] E} {a : ℝ} (ha : 0 < a)
    (hlo : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ) {u : E} (hu : u ≠ 0) :
    0 < ⟪u,H u⟫_ℝ ∧ 0 < ‖H u‖^2 := by
  have hD1 : 0 < ⟪u,H u⟫_ℝ :=
    (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hu))).trans_le (hlo u)
  have hHu : H u ≠ 0 := by
    intro hh
    rw [hh,inner_zero_right] at hD1
    exact lt_irrefl _ hD1
  exact ⟨hD1,sq_pos_of_pos (norm_pos_iff.mpr hHu)⟩

theorem rawIntervalScale_pos {H : E →ₗ[ℝ] E} {a η : ℝ}
    (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hlo : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ) {u : E} (hu : u ≠ 0) :
    0 < rawIntervalScale H a η u := by
  obtain ⟨hD1,hD2⟩ := frozen_moments_pos ha hlo hu
  unfold rawIntervalScale
  by_cases hη : η=0
  · simpa only [hη,zero_mul,sub_zero,one_mul,zero_add] using mul_pos hD1 ha
  · have hηp : 0 < η := lt_of_le_of_ne hη0 (Ne.symm hη)
    exact add_pos_of_pos_of_nonneg (mul_pos hηp hD2)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr hη1) hD1.le) ha.le)

theorem rawIntervalWeight_energy_bounds {H : E →ₗ[ℝ] E} {a b η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ ∧ ⟪x,H x⟫_ℝ ≤ b*‖x‖^2)
    {u : E} (hu : u ≠ 0) (x : E) :
    rawIntervalScale H a η u*‖x‖^2 ≤ ⟪x,(rawIntervalWeight H η u) x⟫_ℝ ∧
    ⟪x,(rawIntervalWeight H η u) x⟫_ℝ ≤ ((b/a)*rawIntervalScale H a η u)*‖x‖^2 := by
  have hD1 := (frozen_moments_pos ha (fun x => (hQ x).1) hu).1
  have hc0 : 0 ≤ η*‖H u‖^2 := mul_nonneg hη0 (sq_nonneg _)
  have hc1 : 0 ≤ (1-η)*⟪u,H u⟫_ℝ := mul_nonneg (sub_nonneg.mpr hη1) hD1.le
  have hl := mul_le_mul_of_nonneg_left (hQ x).1 hc1
  have hh := mul_le_mul_of_nonneg_left (hQ x).2 hc1
  have hκ : 1 ≤ b/a := (le_div_iff ha).2 (by simpa using hab)
  have hcm : η*‖H u‖^2+(1-η)*⟪u,H u⟫_ℝ*b ≤ (b/a)*rawIntervalScale H a η u := by
    have hc := mul_le_mul_of_nonneg_right hκ hc0
    have hid : (b/a)*rawIntervalScale H a η u =
        (b/a)*(η*‖H u‖^2)+(1-η)*⟪u,H u⟫_ℝ*b := by
      unfold rawIntervalScale
      field_simp
      <;> ring
    rw [hid]
    nlinarith only [hc]
  simp only [rawIntervalWeight,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
    inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq]
  constructor
  · unfold rawIntervalScale
    nlinarith only [hl]
  · have hcm' := mul_le_mul_of_nonneg_right hcm (sq_nonneg ‖x‖)
    nlinarith only [hh,hcm']

theorem intervalScale_pos {H : E →ₗ[ℝ] E} {a η : ℝ}
    (ha : 0 < a) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hlo : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ) (u : E) :
    0 < intervalScale H a η u := by
  unfold intervalScale
  split_ifs with hu
  · norm_num
  · exact rawIntervalScale_pos ha hη0 hη1 hlo hu

theorem intervalWeight_energy_bounds {H : E →ₗ[ℝ] E} {a b η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ ∧ ⟪x,H x⟫_ℝ ≤ b*‖x‖^2)
    (u x : E) :
    intervalScale H a η u*‖x‖^2 ≤ ⟪x,(intervalWeight H η u) x⟫_ℝ ∧
    ⟪x,(intervalWeight H η u) x⟫_ℝ ≤ ((b/a)*intervalScale H a η u)*‖x‖^2 := by
  by_cases hu : u=0
  · simp only [intervalScale,intervalWeight,if_pos hu,LinearMap.id_apply,
      real_inner_self_eq_norm_sq,one_mul,mul_one,le_refl,true_and]
    exact le_mul_of_one_le_left (sq_nonneg _) ((le_div_iff ha).2 (by simpa using hab))
  · simpa only [intervalScale,intervalWeight,if_neg hu] using
      rawIntervalWeight_energy_bounds ha hab hη0 hη1 hQ hu x

/-- Exact equality with the convex interpolation of the actual frozen BB endpoints. -/
theorem rawIntervalWeight_alpha {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {a : ℝ}
    (ha : 0 < a) (hlo : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ)
    (η : ℝ) {u : E} (hu : u ≠ 0) :
    weightedAlpha H (rawIntervalWeight H η u) u = BB.Secant.blend η u (H u) := by
  obtain ⟨hD1,hD2⟩ := frozen_moments_pos ha hlo hu
  have hden : ⟪u,(rawIntervalWeight H η u) (H u)⟫_ℝ = ⟪u,H u⟫_ℝ*‖H u‖^2 := by
    simp only [rawIntervalWeight,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
      inner_add_right,real_inner_smul_right]
    rw [← hH u (H u),real_inner_self_eq_norm_sq]
    ring
  unfold weightedAlpha
  rw [hden]
  simp only [rawIntervalWeight,LinearMap.add_apply,LinearMap.smul_apply,LinearMap.id_apply,
    inner_add_right,real_inner_smul_right,real_inner_self_eq_norm_sq,
    BB.Secant.blend,BB.Secant.bb1,BB.Secant.bb2]
  field_simp [hD1.ne',hD2.ne']
  <;> ring

theorem intervalWeight_alpha {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {a : ℝ}
    (ha : 0 < a) (hlo : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ)
    (η : ℝ) (u : E) :
    weightedAlpha H (intervalWeight H η u) u = BB.Secant.blend η u (H u) := by
  by_cases hu : u=0
  · subst u
    simp [weightedAlpha,BB.Secant.blend,BB.Secant.bb1,BB.Secant.bb2]
  · simpa only [intervalWeight,if_neg hu] using rawIntervalWeight_alpha hH ha hlo η hu

/-- The realized weight is positive definite, not merely semidefinite. -/
theorem intervalWeight_posDef {H : E →ₗ[ℝ] E} {a b η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ ∧ ⟪x,H x⟫_ℝ ≤ b*‖x‖^2)
    (u : E) : ∀ x : E, x ≠ 0 → 0 < ⟪x,(intervalWeight H η u) x⟫_ℝ := by
  intro x hx
  exact (mul_pos (intervalScale_pos ha hη0 hη1 (fun x => (hQ x).1) u)
    (sq_pos_of_pos (norm_pos_iff.mpr hx))).trans_le
    (intervalWeight_energy_bounds ha hab hη0 hη1 hQ u x).1

/-- This identifies the entire frozen pair map, including its zero-gradient branch. -/
theorem intervalWeight_stateMap {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {a : ℝ}
    (ha : 0 < a) (hlo : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ)
    (η : ℝ) (z : E × E) :
    stateMap H (intervalWeight H η z.1) z =
      (z.2,z.2-(BB.Secant.blend η z.1 (H z.1)) • H z.2) := by
  unfold stateMap
  rw [intervalWeight_alpha hH ha hlo]

/-- The explicit realized SPD weight has spectral condition number at most b/a. -/
theorem intervalWeight_condition [FiniteDimensional ℝ E]
    {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {a b η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hQ : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫_ℝ ∧ ⟪x,H x⟫_ℝ ≤ b*‖x‖^2)
    (u : E) [Nonempty (Module.End.Eigenvalues (intervalWeight H η u))] :
    spectralConditionNumber (intervalWeight H η u) ≤ b/a := by
  apply (condition_iff_energy_bounds (intervalWeight_symmetric hH η u)
    (intervalWeight_posDef ha hab hη0 hη1 hQ u)
    (div_nonneg (ha.trans_le hab).le ha.le)).2
  exact ⟨intervalScale H a η u,intervalScale_pos ha hη0 hη1 (fun x => (hQ x).1) u,
    intervalWeight_energy_bounds ha hab hη0 hη1 hQ u⟩

end BB.Operator
