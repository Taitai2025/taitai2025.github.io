import BB.UniversalFinite
import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Algebra.Algebra.Spectrum

/-!
# Approximate eigenvectors at actual spectral endpoints

Coercivity implies invertibility by the proved Lax--Milgram theorem. Hence a
spectral endpoint admits unit vectors with arbitrarily close Rayleigh values.
A variance inequality, proved by finite-dimensional compression, converts these
Rayleigh estimates into norm-small eigenvector residuals.
-/

namespace BB
noncomputable section
open Filter
open scoped BigOperators Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma normalized_rayleigh (A : E →L[ℝ] E) (x : E) :
    inner (𝕜 := ℝ) (‖x‖⁻¹ • x) (A (‖x‖⁻¹ • x)) =
      inner (𝕜 := ℝ) x (A x) / ‖x‖^2 := by
  simp only [map_smul, inner_smul_left, inner_smul_right, conj_trivial, smul_eq_mul,
    div_eq_mul_inv, inv_pow]
  ring

lemma quadratic_lower_of_unit_lower (A : E →L[ℝ] E) (c : ℝ)
    (hunit : ∀ x : E, ‖x‖ = 1 → c ≤ inner (𝕜 := ℝ) x (A x)) :
    ∀ x : E, c * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hv : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel hn.ne']
    have h := hunit (‖x‖⁻¹ • x) hv
    rw [normalized_rayleigh] at h
    exact (le_div_iff (sq_pos_of_pos hn)).mp h

lemma quadratic_upper_of_unit_upper (A : E →L[ℝ] E) (c : ℝ)
    (hunit : ∀ x : E, ‖x‖ = 1 → inner (𝕜 := ℝ) x (A x) ≤ c) :
    ∀ x : E, inner (𝕜 := ℝ) x (A x) ≤ c * ‖x‖^2 := by
  intro x
  by_cases hx : x = 0
  · simp [hx]
  · have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hv : ‖‖x‖⁻¹ • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel hn.ne']
    have h := hunit (‖x‖⁻¹ • x) hv
    rw [normalized_rayleigh] at h
    exact (div_le_iff (sq_pos_of_pos hn)).mp h

lemma coercive_operator_isUnit [CompleteSpace E] (T : E →L[ℝ] E) (c : ℝ) (hc : 0 < c)
    (hbound : ∀ x : E, c * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (T x)) : IsUnit T := by
  let B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp T
  have hB : IsCoercive B := by
    refine ⟨c, hc, ?_⟩
    intro x
    change c * ‖x‖ * ‖x‖ ≤ inner (𝕜 := ℝ) (T x) x
    rw [real_inner_comm]
    simpa only [pow_two, mul_assoc] using hbound x
  let e := hB.continuousLinearEquivOfBilin
  have he : e.toContinuousLinearMap = T := by
    ext x
    apply ext_inner_right ℝ
    intro y
    exact hB.continuousLinearEquivOfBilin_apply x y
  exact ⟨e.toUnit, he⟩

lemma spectrum_lower_rayleigh [CompleteSpace E] (A : E →L[ℝ] E) (a δ : ℝ)
    (ha : a ∈ spectrum ℝ A) (hδ : 0 < δ) :
    ∃ x : E, ‖x‖ = 1 ∧ inner (𝕜 := ℝ) x (A x) < a + δ := by
  by_contra h
  push_neg at h
  have hglobal := quadratic_lower_of_unit_lower A (a + δ) h
  have hco : ∀ x : E, δ * ‖x‖^2 ≤ inner (𝕜 := ℝ) x ((A - a • 1) x) := by
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    linarith [hglobal x]
  have hu := coercive_operator_isUnit (A - a • 1) δ hδ hco
  apply (spectrum.mem_iff.mp ha)
  rw [Algebra.algebraMap_eq_smul_one]
  simpa only [neg_sub] using hu.neg

lemma spectrum_upper_rayleigh [CompleteSpace E] (A : E →L[ℝ] E) (b δ : ℝ)
    (hb : b ∈ spectrum ℝ A) (hδ : 0 < δ) :
    ∃ x : E, ‖x‖ = 1 ∧ b - δ < inner (𝕜 := ℝ) x (A x) := by
  by_contra h
  push_neg at h
  have hglobal := quadratic_upper_of_unit_upper A (b - δ) h
  have hco : ∀ x : E, δ * ‖x‖^2 ≤ inner (𝕜 := ℝ) x ((b • 1 - A) x) := by
    intro x
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq]
    linarith [hglobal x]
  have hu := coercive_operator_isUnit (b • 1 - A) δ hδ hco
  apply (spectrum.mem_iff.mp hb)
  simpa only [Algebra.algebraMap_eq_smul_one] using hu


section Finite
variable [FiniteDimensional ℝ E]

lemma finite_operator_variance_lower {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (H x) ∧
      inner (𝕜 := ℝ) x (H x) ≤ b * ‖x‖^2) (x : E) :
    ‖H x - a • x‖^2 ≤ (b - a) * (inner (𝕜 := ℝ) x (H x) - a * ‖x‖^2) := by
  have hLambda := eigenvalue_bounds hH a b hbounds
  have hcoord : eigenCoordinates hH (H x - a • x) =
      fun i => (eigenValues hH i - a) * eigenCoordinates hH x i := by
    funext i
    change (hH.eigenvectorBasis rfl).repr (H x - a • x) i = _
    rw [map_sub, map_smul]
    change eigenCoordinates hH (H x) i - a * eigenCoordinates hH x i = _
    rw [eigen_coordinates_apply]
    ring
  rw [← eigen_coordinates_energy hH (H x - a • x), hcoord, eigen_coordinates_inner,
    ← eigen_coordinates_energy hH x]
  unfold energy
  calc
    (∑ i, ((eigenValues hH i - a) * eigenCoordinates hH x i)^2) ≤
        ∑ i, (b - a) * ((eigenValues hH i - a) * (eigenCoordinates hH x i)^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hq : (eigenValues hH i - a)^2 ≤ (b - a) * (eigenValues hH i - a) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (hLambda i).1) (sub_nonneg.mpr (hLambda i).2)]
      simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_right hq (sq_nonneg (eigenCoordinates hH x i))
    _ = (b - a) * ∑ i, (eigenValues hH i - a) * (eigenCoordinates hH x i)^2 :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      congr 1
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

lemma finite_operator_variance_upper {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (H x) ∧
      inner (𝕜 := ℝ) x (H x) ≤ b * ‖x‖^2) (x : E) :
    ‖H x - b • x‖^2 ≤ (b - a) * (b * ‖x‖^2 - inner (𝕜 := ℝ) x (H x)) := by
  have hLambda := eigenvalue_bounds hH a b hbounds
  have hcoord : eigenCoordinates hH (H x - b • x) =
      fun i => (eigenValues hH i - b) * eigenCoordinates hH x i := by
    funext i
    change (hH.eigenvectorBasis rfl).repr (H x - b • x) i = _
    rw [map_sub, map_smul]
    change eigenCoordinates hH (H x) i - b * eigenCoordinates hH x i = _
    rw [eigen_coordinates_apply]
    ring
  rw [← eigen_coordinates_energy hH (H x - b • x), hcoord, eigen_coordinates_inner,
    ← eigen_coordinates_energy hH x]
  unfold energy
  calc
    (∑ i, ((eigenValues hH i - b) * eigenCoordinates hH x i)^2) ≤
        ∑ i, (b - a) * ((b - eigenValues hH i) * (eigenCoordinates hH x i)^2) := by
      apply Finset.sum_le_sum
      intro i _
      have hq : (eigenValues hH i - b)^2 ≤ (b - a) * (b - eigenValues hH i) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr (hLambda i).1) (sub_nonneg.mpr (hLambda i).2)]
      simpa only [mul_pow, mul_assoc] using mul_le_mul_of_nonneg_right hq (sq_nonneg (eigenCoordinates hH x i))
    _ = (b - a) * ∑ i, (b - eigenValues hH i) * (eigenCoordinates hH x i)^2 :=
      (Finset.mul_sum _ _ _).symm
    _ = _ := by
      congr 1
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]

end Finite

lemma operator_variance_lower (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) (x : E) :
    ‖A x - a • x‖^2 ≤ (b - a) * (inner (𝕜 := ℝ) x (A x) - a * ‖x‖^2) := by
  let g : ℕ → E := fun _ => x
  let V := trajectorySpace A g 0
  let v : V := ⟨x, gradient_mem_trajectorySpace A g 0 0 (by omega)⟩
  have hAv : A (v : E) ∈ V := image_mem_trajectorySpace A g 0 0 (by omega)
  have he : (operatorCompression A V v : E) = A x := orthogonalProjection_eq_self_iff.mpr hAv
  have h := finite_operator_variance_lower (compression_symmetric A hA V) a b
    (compression_bounds A V a b hbounds) v
  change ‖(operatorCompression A V v : E) - a • x‖^2 ≤
    (b - a) * (inner (𝕜 := ℝ) x (operatorCompression A V v : E) - a * ‖x‖^2) at h
  simpa only [he] using h

lemma operator_variance_upper (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) (x : E) :
    ‖A x - b • x‖^2 ≤ (b - a) * (b * ‖x‖^2 - inner (𝕜 := ℝ) x (A x)) := by
  let g : ℕ → E := fun _ => x
  let V := trajectorySpace A g 0
  let v : V := ⟨x, gradient_mem_trajectorySpace A g 0 0 (by omega)⟩
  have hAv : A (v : E) ∈ V := image_mem_trajectorySpace A g 0 0 (by omega)
  have he : (operatorCompression A V v : E) = A x := orthogonalProjection_eq_self_iff.mpr hAv
  have h := finite_operator_variance_upper (compression_symmetric A hA V) a b
    (compression_bounds A V a b hbounds) v
  change ‖(operatorCompression A V v : E) - b • x‖^2 ≤
    (b - a) * (b * ‖x‖^2 - inner (𝕜 := ℝ) x (operatorCompression A V v : E)) at h
  simpa only [he] using h

lemma spectrum_approximate_lower [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a ≤ b)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖A x - a • x‖ < ε := by
  let δ := ε^2 / (b - a + 1)
  have hden : 0 < b - a + 1 := by linarith
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
  have hδeq : (b - a + 1) * δ = ε^2 := by
    dsimp [δ]
    exact mul_div_cancel₀ _ hden.ne'
  obtain ⟨x, hx, hray⟩ := spectrum_lower_rayleigh A a δ haspec hδ
  have hv := operator_variance_lower A hA a b hbounds x
  rw [hx, one_pow, mul_one] at hv
  have hmul := mul_le_mul_of_nonneg_left (le_of_lt (show inner (𝕜 := ℝ) x (A x) - a < δ by linarith))
    (sub_nonneg.mpr hab)
  have hsmall : (b - a) * δ < ε^2 := by nlinarith [hδeq]
  refine ⟨x, hx, ?_⟩
  have hsq : ‖A x - a • x‖^2 < ε^2 := hv.trans_lt (hmul.trans_lt hsmall)
  nlinarith only [hsq, norm_nonneg (A x - a • x), hε]

lemma spectrum_approximate_upper [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a ≤ b)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2)
    (hbspec : b ∈ spectrum ℝ A) (ε : ℝ) (hε : 0 < ε) :
    ∃ x : E, ‖x‖ = 1 ∧ ‖A x - b • x‖ < ε := by
  let δ := ε^2 / (b - a + 1)
  have hden : 0 < b - a + 1 := by linarith
  have hδ : 0 < δ := div_pos (sq_pos_of_pos hε) hden
  have hδeq : (b - a + 1) * δ = ε^2 := by
    dsimp [δ]
    exact mul_div_cancel₀ _ hden.ne'
  obtain ⟨x, hx, hray⟩ := spectrum_upper_rayleigh A b δ hbspec hδ
  have hv := operator_variance_upper A hA a b hbounds x
  rw [hx, one_pow, mul_one] at hv
  have hmul := mul_le_mul_of_nonneg_left (le_of_lt (show b - inner (𝕜 := ℝ) x (A x) < δ by linarith))
    (sub_nonneg.mpr hab)
  have hsmall : (b - a) * δ < ε^2 := by nlinarith [hδeq]
  refine ⟨x, hx, ?_⟩
  have hsq : ‖A x - b • x‖^2 < ε^2 := hv.trans_lt (hmul.trans_lt hsmall)
  nlinarith only [hsq, norm_nonneg (A x - b • x), hε]


lemma unit_approximate_sequence (R : E → E)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ x : E, ‖x‖ = 1 ∧ ‖R x‖ < ε) :
    ∃ p : ℕ → E, (∀ n, ‖p n‖ = 1) ∧
      Tendsto (fun n => ‖R (p n)‖) atTop (𝓝 0) := by
  have hex : ∀ n : ℕ, ∃ x : E, ‖x‖ = 1 ∧ ‖R x‖ < 1 / ((n : ℝ) + 1) := by
    intro n
    exact happrox _ (by positivity)
  choose p hpunit hpres using hex
  refine ⟨p, hpunit, ?_⟩
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n => norm_nonneg (R (p n)))
    (fun n => (hpres n).le)

/-- Actual endpoint spectrum membership supplies the unit-vector sequences
used to test sharp uniform rates even when neither endpoint is an eigenvalue. -/
lemma spectrum_approximate_endpoint_sequences [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a ≤ b)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    ∃ p q : ℕ → E, (∀ n, ‖p n‖ = 1 ∧ ‖q n‖ = 1) ∧
      Tendsto (fun n => ‖A (p n) - a • p n‖) atTop (𝓝 0) ∧
      Tendsto (fun n => ‖A (q n) - b • q n‖) atTop (𝓝 0) := by
  obtain ⟨p, hpunit, hp⟩ := unit_approximate_sequence (fun x => A x - a • x)
    (spectrum_approximate_lower A hA a b hab hbounds haspec)
  obtain ⟨q, hqunit, hq⟩ := unit_approximate_sequence (fun x => A x - b • x)
    (spectrum_approximate_upper A hA a b hab hbounds hbspec)
  exact ⟨p, q, fun n => ⟨hpunit n, hqunit n⟩, hp, hq⟩

end
end BB
