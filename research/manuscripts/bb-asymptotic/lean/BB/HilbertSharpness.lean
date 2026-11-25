import BB.LinearCoordinates
import BB.TwoPoint
import BB.Asymptotics

/-!
# Actual Hilbert-space endpoint eigenvector orbits

The operator and trajectory live in an arbitrary real inner-product space;
no finite-dimensional spectral decomposition is used.  Distinct symmetric
eigenvectors are orthogonal, and the balanced two-eigenvector orbit attains
the sharp norm factor at every step.
-/

noncomputable section

namespace BB

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

theorem distinct_eigenvectors_inner_zero (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (a b : ℝ) (hab : a ≠ b) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) : ⟪p, q⟫ = 0 := by
  have h := hH p q
  rw [hp, hq, real_inner_smul_left, inner_smul_right] at h
  have hzero : (a-b) * ⟪p, q⟫ = 0 := by nlinarith
  exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hab)

theorem orthogonal_combination_norm_sq (p q : E) (horth : ⟪p, q⟫ = 0) (u v : ℝ) :
    ‖u • p + v • q‖^2 = u^2 * ‖p‖^2 + v^2 * ‖q‖^2 := by
  simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_smul_left, inner_smul_right, horth, mul_zero, zero_mul, add_zero]

theorem orthogonal_combination_norm (p q : E) (horth : ⟪p, q⟫ = 0) (u v : ℝ) :
    ‖u • p + v • q‖ = normTwo (u*‖p‖) (v*‖q‖) := by
  unfold normTwo
  calc
    ‖u • p + v • q‖ = Real.sqrt (‖u • p + v • q‖^2) :=
      (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt ((u*‖p‖)^2+(v*‖q‖)^2) := by
      rw [orthogonal_combination_norm_sq p q horth]
      congr 1
      ring

theorem eigen_combination_energy_inner (H : E →ₗ[ℝ] E) (a b : ℝ) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (horth : ⟪p, q⟫ = 0) (u v : ℝ) :
    ⟪u • p + v • q, H (u • p + v • q)⟫ =
      a * u^2 * ‖p‖^2 + b * v^2 * ‖q‖^2 := by
  have horth' : ⟪q, p⟫ = 0 := by rw [real_inner_comm, horth]
  simp only [map_add, map_smul, hp, hq, inner_add_left, inner_add_right,
    real_inner_smul_left, inner_smul_right, horth, horth',
    real_inner_self_eq_norm_sq, mul_zero, zero_mul, add_zero, zero_add]
  ring

theorem operator_bb1_two_eigenvectors (H : E →ₗ[ℝ] E) (a b : ℝ) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (horth : ⟪p, q⟫ = 0) (u v : ℝ) :
    operatorBB1 H (u • p + v • q) = bb1Two a b (u*‖p‖) (v*‖q‖) := by
  unfold operatorBB1 bb1Two
  rw [orthogonal_combination_norm_sq p q horth,
    eigen_combination_energy_inner H a b p q hp hq horth]
  congr 1 <;> ring

theorem operator_step_two_eigenvectors (H : E →ₗ[ℝ] E) (a b : ℝ) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (α u v : ℝ) :
    operatorGradientStep H α (u • p + v • q) =
      ((1-α*a)*u) • p + ((1-α*b)*v) • q := by
  have hleft : (1-α*a)*u = u-α*(u*a) := by ring
  have hright : (1-α*b)*v = v-α*(v*b) := by ring
  rw [hleft, hright]
  simp only [operatorGradientStep, map_add, map_smul, hp, hq,
    smul_add, smul_smul, sub_smul]
  abel

def hilbertEndpointOrbit (a b : ℝ) (p q : E) (n : ℕ) : E :=
  (rate a b)^n • p + (-(rate a b))^n • q

theorem hilbert_endpoint_orbit_step (H : E →ₗ[ℝ] E) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (n : ℕ) :
    operatorGradientStep H (2/(a+b)) (hilbertEndpointOrbit a b p q n) =
      hilbertEndpointOrbit a b p q (n+1) := by
  have hs : a+b ≠ 0 := ne_of_gt (by linarith : 0 < a+b)
  unfold hilbertEndpointOrbit
  rw [operator_step_two_eigenvectors H a b p q hp hq,
    endpoint_left_multiplier hs, endpoint_right_multiplier hs]
  congr 1 <;> congr 1 <;> rw [pow_succ] <;> ring

theorem hilbert_endpoint_orbit_quotient (H : E →ₗ[ℝ] E) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q)
    (horth : ⟪p, q⟫ = 0) (hp0 : p ≠ 0) (hbalance : ‖p‖ = ‖q‖) (n : ℕ) :
    operatorBB1 H (hilbertEndpointOrbit a b p q n) = 2/(a+b) := by
  rw [hilbertEndpointOrbit, operator_bb1_two_eigenvectors H a b p q hp hq horth]
  apply balanced_bb1_step
  · exact mul_ne_zero (pow_ne_zero n (rate_pos ha hab).ne') (norm_ne_zero_iff.mpr hp0)
  · exact endpoint_balance_orbit (rate a b) ‖p‖ ‖q‖ (by rw [hbalance]) n

theorem hilbert_endpoint_orbit_norm (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (p q : E) (horth : ⟪p, q⟫ = 0) (n : ℕ) :
    ‖hilbertEndpointOrbit a b p q n‖ = (rate a b)^n * ‖hilbertEndpointOrbit a b p q 0‖ := by
  have hzero : ‖hilbertEndpointOrbit a b p q 0‖ = normTwo ‖p‖ ‖q‖ := by
    simpa only [hilbertEndpointOrbit, pow_zero, one_smul, one_mul] using
      orthogonal_combination_norm p q horth 1 1
  rw [hilbertEndpointOrbit, orthogonal_combination_norm p q horth, hzero]
  exact endpoint_norm_orbit (rate_pos ha hab).le ‖p‖ ‖q‖ n

/-- An actual nonterminating matched delayed BB1 trajectory in an arbitrary
real inner-product space attains the endpoint rate at every step. -/
theorem hilbert_endpoint_matched_orbit (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (hp0 : p ≠ 0) (hbalance : ‖p‖ = ‖q‖) :
    let g := hilbertEndpointOrbit a b p q
    g 0 ≠ 0 ∧ 0 < operatorBB1 H (g 0) ∧
      g 1 = operatorGradientStep H (operatorBB1 H (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate a b)^n * ‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖ / ‖g 0‖) = rate a b := by
  dsimp only
  have horth := distinct_eigenvectors_inner_zero H hH a b hab.ne p q hp hq
  have h0 : hilbertEndpointOrbit a b p q 0 ≠ 0 := by
    intro hz
    have hsq := orthogonal_combination_norm_sq p q horth 1 1
    simp only [one_smul, one_pow, one_mul] at hsq
    have hz' : p+q = 0 := by simpa only [hilbertEndpointOrbit, pow_zero, one_smul] using hz
    rw [hz', norm_zero] at hsq
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hp0), sq_nonneg ‖q‖]
  have hquot := hilbert_endpoint_orbit_quotient H a b ha hab p q hp hq horth hp0 hbalance
  have hnorm := hilbert_endpoint_orbit_norm a b ha hab p q horth
  refine ⟨h0, ?_, ?_, ?_, hnorm, ?_⟩
  · rw [hquot 0]
    exact div_pos (by norm_num) (by linarith)
  · rw [hquot 0]
    exact (hilbert_endpoint_orbit_step H a b ha hab p q hp hq 0).symm
  · intro n
    rw [hquot n]
    exact (hilbert_endpoint_orbit_step H a b ha hab p q hp hq (n+1)).symm
  · have heq : (fun n => ‖hilbertEndpointOrbit a b p q n‖ / ‖hilbertEndpointOrbit a b p q 0‖) =
        (fun n => (1 : ℝ) * (rate a b)^n) := by
      funext n
      rw [hnorm n, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr h0), one_mul]
    rw [heq]
    exact rootFactor_geometric 1 _ zero_lt_one (rate_pos ha hab).le

/-- Endpoint eigenvalues suffice for exact attainment; equal masses are obtained
by normalizing arbitrary nonzero endpoint eigenvectors. -/
theorem hilbert_endpoint_eigenvalues_attain (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hep : ∃ p : E, p ≠ 0 ∧ H p = a • p)
    (heq : ∃ q : E, q ≠ 0 ∧ H q = b • q) :
    ∃ g : ℕ → E, g 0 ≠ 0 ∧ 0 < operatorBB1 H (g 0) ∧
      g 1 = operatorGradientStep H (operatorBB1 H (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate a b)^n * ‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖ / ‖g 0‖) = rate a b := by
  obtain ⟨p, hp0, hp⟩ := hep
  obtain ⟨q, hq0, hq⟩ := heq
  let p' : E := ‖p‖⁻¹ • p
  let q' : E := ‖q‖⁻¹ • q
  have hpn : ‖p'‖ = 1 := by
    dsimp [p']; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hp0)),
      inv_mul_cancel (norm_ne_zero_iff.mpr hp0)]
  have hqn : ‖q'‖ = 1 := by
    dsimp [q']; rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hq0)),
      inv_mul_cancel (norm_ne_zero_iff.mpr hq0)]
  have hp' : H p' = a • p' := by
    dsimp [p']; rw [map_smul, hp, smul_smul, smul_smul, mul_comm]
  have hq' : H q' = b • q' := by
    dsimp [q']; rw [map_smul, hq, smul_smul, smul_smul, mul_comm]
  have hp0' : p' ≠ 0 := by intro hz; simp [hz] at hpn
  exact ⟨hilbertEndpointOrbit a b p' q',
    hilbert_endpoint_matched_orbit H hH a b ha hab p' q' hp' hq' hp0' (hpn.trans hqn.symm)⟩

end BB
