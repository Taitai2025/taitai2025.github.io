import BB.FunctionalEmbedding
import BB.WeightedRates

/-!
# Dimension-independent weighted estimates and BB2 compression

The finite weighted estimate uses explicit bounds on the weight, so its
constant is independent of the dimension and the locations of eigenvalues.
Exact finite-dimensional compression then transfers BB2 estimates to arbitrary
real inner-product spaces.
-/

universe u

namespace BB
noncomputable section
open Filter
open scoped BigOperators

def weightedEnvelopeConstant (C γ M m W : ℝ) : ℝ :=
  ((Real.sqrt m)⁻¹ * Real.sqrt W) *
    (1 + C * (((Real.sqrt m)⁻¹ * Real.sqrt W) * M) / γ)

lemma weighted_envelope_constant_pos (C γ M m W : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M) (hm : 0 < m) (hW : 0 < W) :
    0 < weightedEnvelopeConstant C γ M m W := by
  unfold weightedEnvelopeConstant
  have hs : 0 < (Real.sqrt m)⁻¹ * Real.sqrt W :=
    mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr hm)) (Real.sqrt_pos.mpr hW)
  exact mul_pos hs (by positivity)

section Diagonal
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_gradient_envelope_from_prefix (lam ψ : ι → ℝ) (C γ M m W : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M) (hm : 0 < m) (hW : 0 < W)
    (hψlo : ∀ i, m ≤ ψ i) (hψhi : ∀ i, ψ i ≤ W)
    (hprefix : ∀ n χ, prefixProduct (stateGrowth lam) (spectralMap lam) n χ ≤ C * γ^n)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1)))
    (hfirst : normDiag (g 1) ≤ M * normDiag (g 0)) (n : ℕ) :
    normDiag (g n) ≤ weightedEnvelopeConstant C γ M m W * γ^n * normDiag (g 0) := by
  let S := (Real.sqrt m)⁻¹ * Real.sqrt W
  have hsm : 0 < (Real.sqrt m)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  have hsW : 0 < Real.sqrt W := Real.sqrt_pos.mpr hW
  have hS : 0 < S := mul_pos hsm hsW
  have hψ : ∀ i, 0 < ψ i := fun i => hm.trans_le (hψlo i)
  have hfirst' : normDiag (spectralScale ψ (g 1)) ≤ (S * M) * normDiag (spectralScale ψ (g 0)) := by
    calc
      normDiag (spectralScale ψ (g 1)) ≤ Real.sqrt W * normDiag (g 1) :=
        (spectral_scale_norm_bounds ψ (g 1) m W hm hψlo hψhi).2
      _ ≤ Real.sqrt W * (M * normDiag (g 0)) := mul_le_mul_of_nonneg_left hfirst hsW.le
      _ ≤ Real.sqrt W * (M * ((Real.sqrt m)⁻¹ * normDiag (spectralScale ψ (g 0)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_le_inverse_scale ψ (g 0) m W hm hψlo hψhi) hM) hsW.le
      _ = (S * M) * normDiag (spectralScale ψ (g 0)) := by dsimp [S]; ring
  have henv := gradient_envelope_from_prefix lam C γ (S * M) hC hγ (mul_nonneg hS.le hM) hprefix
    (fun k => spectralScale ψ (g k)) (spectral_scale_energy_pos ψ hψ hg0)
    (weighted_delayed_update_conjugacy lam ψ g (fun i => (hψ i).le) hupdate) hfirst' n
  calc
    normDiag (g n) ≤ (Real.sqrt m)⁻¹ * normDiag (spectralScale ψ (g n)) :=
      norm_le_inverse_scale ψ (g n) m W hm hψlo hψhi
    _ ≤ (Real.sqrt m)⁻¹ * ((1 + C * (S * M) / γ) * γ^n * normDiag (spectralScale ψ (g 0))) :=
      mul_le_mul_of_nonneg_left henv hsm.le
    _ ≤ (Real.sqrt m)⁻¹ * ((1 + C * (S * M) / γ) * γ^n * (Real.sqrt W * normDiag (g 0))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spectral_scale_norm_bounds ψ (g 0) m W hm hψlo hψhi).2
          (mul_nonneg (by positivity) (pow_nonneg hγ.le n))) hsm.le
    _ = weightedEnvelopeConstant C γ M m W * γ^n * normDiag (g 0) := by
      dsimp [weightedEnvelopeConstant, S]
      ring

end Diagonal

/-- The constant is chosen before dimension, spectrum, weight, and trajectory. -/
lemma uniform_weighted_gradient_envelope (a b γ M m W : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hγ : rate a b < γ)
    (hM : 0 ≤ M) (hm : 0 < m) (hW : 0 < W) :
    ∃ K : ℝ, 0 < K ∧ ∀ (d : ℕ) (lam ψ : Fin d → ℝ),
      (∀ i, a ≤ lam i ∧ lam i ≤ b) → (∀ i, m ≤ ψ i) → (∀ i, ψ i ≤ W) →
      ∀ (g : ℕ → Fin d → ℝ), 0 < energy (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) →
      normDiag (g 1) ≤ M * normDiag (g 0) →
      ∀ n, normDiag (g n) ≤ K * γ^n * normDiag (g 0) := by
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  obtain ⟨C, hC, hU⟩ := uniform_spectral_envelope_exists a b γ ha hab hγ
  refine ⟨weightedEnvelopeConstant C γ M m W,
    weighted_envelope_constant_pos C γ M m W hC hγpos hM hm hW, ?_⟩
  intro d lam ψ hlam hψlo hψhi g hg0 hupdate hfirst n
  exact weighted_gradient_envelope_from_prefix lam ψ C γ M m W hC hγpos hM hm hW
    hψlo hψhi (hU d lam hlam) g hg0 hupdate hfirst n

section Operators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def operatorBB2 (H : E →ₗ[ℝ] E) (g : E) : ℝ :=
  inner (𝕜 := ℝ) g (H g) / ‖H g‖^2

section Finite
variable [FiniteDimensional ℝ E]

lemma eigen_coordinates_bb2_quotient {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) :
    operatorBB2 H g = weightedBB (eigenValues hH) (eigenValues hH) (eigenCoordinates hH g) := by
  have hd : (∑ i, eigenValues hH i * eigenValues hH i * (eigenCoordinates hH g i)^2) = ‖H g‖^2 := by
    rw [← eigen_coordinates_energy hH (H g)]
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    rw [eigen_coordinates_apply]
    ring
  unfold operatorBB2 weightedBB weightedEnergy
  rw [hd, eigen_coordinates_inner]

lemma eigen_coordinates_bb2_orbit {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (g : ℕ → E)
    (hupdate : ∀ n, g (n + 2) = operatorGradientStep H (operatorBB2 H (g n)) (g (n + 1))) :
    ∀ n, eigenCoordinates hH (g (n + 2)) = gradientUpdate (eigenValues hH)
      (weightedBB (eigenValues hH) (eigenValues hH) (eigenCoordinates hH (g n)))
      (eigenCoordinates hH (g (n + 1))) := by
  intro n
  rw [hupdate n, eigen_coordinates_update, eigen_coordinates_bb2_quotient]

lemma universal_finite_bb2_operator_envelope {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b C γ M : ℝ) (ha : 0 < a) (hab : a ≤ b) (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hU : UniformSpectralEnvelope a b γ C)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (H x) ∧
      inner (𝕜 := ℝ) x (H x) ≤ b * ‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n + 2) = operatorGradientStep H (operatorBB2 H (g n)) (g (n + 1)))
    (hfirst : ‖g 1‖ ≤ M * ‖g 0‖) (n : ℕ) :
    ‖g n‖ ≤ weightedEnvelopeConstant C γ M a b * γ^n * ‖g 0‖ := by
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hefirst : normDiag (eigenCoordinates hH (g 1)) ≤ M * normDiag (eigenCoordinates hH (g 0)) := by
    simpa only [eigen_coordinates_norm] using hfirst
  have hLambda := eigenvalue_bounds hH a b hbounds
  simpa only [eigen_coordinates_norm] using weighted_gradient_envelope_from_prefix
    (eigenValues hH) (eigenValues hH) C γ M a b hC hγ hM ha (ha.trans_le hab)
    (fun i => (hLambda i).1) (fun i => (hLambda i).2) (hU _ _ hLambda)
    (fun k => eigenCoordinates hH (g k)) he0 (eigen_coordinates_bb2_orbit hH g hupdate) hefirst n

end Finite

lemma compression_bb2_quotient (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (x : V) (hx : A (x : E) ∈ V) :
    operatorBB2 (operatorCompression A V).toLinearMap x = operatorBB2 A.toLinearMap (x : E) := by
  have he : (operatorCompression A V x : E) = A (x : E) :=
    orthogonalProjection_eq_self_iff.mpr hx
  unfold operatorBB2
  change inner (𝕜 := ℝ) x (operatorCompression A V x) / ‖(operatorCompression A V x : E)‖^2 = _
  rw [compression_inner_left, he]
  rfl

def linearBB2Orbit (H : E →ₗ[ℝ] E) (g₀ g₁ : E) : ℕ → E
  | 0 => g₀
  | 1 => g₁
  | n + 2 => operatorGradientStep H (operatorBB2 H (linearBB2Orbit H g₀ g₁ n))
      (linearBB2Orbit H g₀ g₁ (n + 1))

def compressedBB2Trajectory (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ) :
    ℕ → trajectorySpace A g N :=
  linearBB2Orbit (operatorCompression A (trajectorySpace A g N)).toLinearMap
    ⟨g 0, gradient_mem_trajectorySpace A g N 0 (by omega)⟩
    ⟨g 1, gradient_mem_trajectorySpace A g N 1 (by omega)⟩

lemma compressed_bb2_trajectory_matches (A : E →L[ℝ] E) (g : ℕ → E) (N : ℕ)
    (hupdate : ∀ n, g (n + 2) = operatorGradientStep A.toLinearMap
      (operatorBB2 A.toLinearMap (g n)) (g (n + 1))) :
    ∀ j, j ≤ N → (compressedBB2Trajectory A g N j : E) = g j := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    cases j with
    | zero => rfl
    | succ j =>
      cases j with
      | zero => rfl
      | succ k =>
        have hprev := ih k (by omega) (by omega)
        have hcur := ih (k + 1) (by omega) (by omega)
        have hmemPrev : A (compressedBB2Trajectory A g N k : E) ∈ trajectorySpace A g N := by
          rw [hprev]
          exact image_mem_trajectorySpace A g N k (by omega)
        have hmemCur : A (compressedBB2Trajectory A g N (k + 1) : E) ∈ trajectorySpace A g N := by
          rw [hcur]
          exact image_mem_trajectorySpace A g N (k + 1) (by omega)
        change ((operatorGradientStep (operatorCompression A (trajectorySpace A g N)).toLinearMap
            (operatorBB2 (operatorCompression A (trajectorySpace A g N)).toLinearMap
              (compressedBB2Trajectory A g N k)) (compressedBB2Trajectory A g N (k + 1)) :
                trajectorySpace A g N) : E) = g (k + 2)
        rw [compression_bb2_quotient A (trajectorySpace A g N) _ hmemPrev, hprev,
          compression_step A (trajectorySpace A g N) _ _ hmemCur, hcur]
        exact (hupdate k).symm

lemma compressed_bb2_trajectory_update (A : E →L[ℝ] E) (g : ℕ → E) (N n : ℕ) :
    compressedBB2Trajectory A g N (n + 2) =
      operatorGradientStep (operatorCompression A (trajectorySpace A g N)).toLinearMap
        (operatorBB2 (operatorCompression A (trajectorySpace A g N)).toLinearMap
          (compressedBB2Trajectory A g N n)) (compressedBB2Trajectory A g N (n + 1)) := rfl

lemma operator_bb2_envelope_from_universal_finite (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b C γ M : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hU : UniformSpectralEnvelope a b γ C)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n + 2) = operatorGradientStep A.toLinearMap
      (operatorBB2 A.toLinearMap (g n)) (g (n + 1)))
    (hfirst : ‖g 1‖ ≤ M * ‖g 0‖) (n : ℕ) :
    ‖g n‖ ≤ weightedEnvelopeConstant C γ M a b * γ^n * ‖g 0‖ := by
  let V := trajectorySpace A g n
  let v := compressedBB2Trajectory A g n
  have hv0 : v 0 ≠ 0 := by
    intro hz
    exact hg0 (congrArg Subtype.val hz)
  have hvfirst : ‖v 1‖ ≤ M * ‖v 0‖ := hfirst
  have h := universal_finite_bb2_operator_envelope (compression_symmetric A hA V)
    a b C γ M ha hab hC hγ hM hU (compression_bounds A V a b hbounds) v hv0
    (compressed_bb2_trajectory_update A g n) hvfirst n
  change ‖(compressedBB2Trajectory A g n n : E)‖ ≤
    weightedEnvelopeConstant C γ M a b * γ^n * ‖g 0‖ at h
  rw [compressed_bb2_trajectory_matches A g n hupdate n le_rfl] at h
  exact h

lemma positive_operator_bb2_pos_and_upper (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) (x : E) (hx : x ≠ 0) :
    0 < operatorBB2 A.toLinearMap x ∧ operatorBB2 A.toLinearMap x ≤ 1 / a := by
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hlo := (operator_norm_bounds_via_compression A hA a b ha hab hbounds x).1
  have hAx : 0 < ‖A x‖ := (mul_pos ha hx0).trans_le hlo
  have hp : 0 < inner (𝕜 := ℝ) x (A x) := (mul_pos ha (sq_pos_of_pos hx0)).trans_le (hbounds x).1
  constructor
  · exact div_pos hp (sq_pos_of_pos hAx)
  · apply (div_le_div_iff (sq_pos_of_pos hAx) ha).mpr
    have hc := real_inner_le_norm x (A x)
    change inner (𝕜 := ℝ) x (A x) * a ≤ 1 * ‖A x‖^2
    calc
      inner (𝕜 := ℝ) x (A x) * a ≤ (‖x‖ * ‖A x‖) * a := mul_le_mul_of_nonneg_right hc ha.le
      _ = (a * ‖x‖) * ‖A x‖ := by ring
      _ ≤ ‖A x‖ * ‖A x‖ := mul_le_mul_of_nonneg_right hlo hAx.le
      _ = 1 * ‖A x‖^2 := by ring

lemma matched_operator_bb2_first_bound (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) (x : E) (hx : x ≠ 0) :
    ‖operatorGradientStep A.toLinearMap (operatorBB2 A.toLinearMap x) x‖ ≤
      (1 + b / a) * ‖x‖ := by
  obtain ⟨hp, hu⟩ := positive_operator_bb2_pos_and_upper A hA a b ha hab hbounds x hx
  have hn := (operator_norm_bounds_via_compression A hA a b ha hab hbounds x).2
  unfold operatorGradientStep
  calc
    ‖x - operatorBB2 A.toLinearMap x • A x‖ ≤ ‖x‖ + ‖operatorBB2 A.toLinearMap x • A x‖ := norm_sub_le _ _
    _ = ‖x‖ + operatorBB2 A.toLinearMap x * ‖A x‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hp]
    _ ≤ ‖x‖ + (1 / a) * (b * ‖x‖) :=
      add_le_add_left (mul_le_mul hu hn (norm_nonneg _) (by positivity)) _
    _ = (1 + b / a) * ‖x‖ := by ring

end Operators


/-- A common BB2 constant for arbitrary dimensions, Hilbert spaces, operators,
and initial gradients with the prescribed first-step norm bound. -/
lemma bb2_uniform_family_envelope (a b γ M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hγ : rate a b < γ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (A : E →L[ℝ] E), A.toLinearMap.IsSymmetric →
      (∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧ inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) →
      ∀ (g : ℕ → E), g 0 ≠ 0 →
      (∀ n, g (n + 2) = operatorGradientStep A.toLinearMap (operatorBB2 A.toLinearMap (g n)) (g (n + 1))) →
      ‖g 1‖ ≤ M * ‖g 0‖ → ∀ n, ‖g n‖ ≤ K * γ^n * ‖g 0‖ := by
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  obtain ⟨C, hC, hU⟩ := uniform_spectral_envelope_exists a b γ ha hab hγ
  refine ⟨weightedEnvelopeConstant C γ M a b,
    weighted_envelope_constant_pos C γ M a b hC hγpos hM ha (ha.trans_le hab), ?_⟩
  intro E instN instI A hA hbounds g hg0 hupdate hfirst n
  exact operator_bb2_envelope_from_universal_finite A hA a b C γ M ha hab hC hγpos hM hU
    hbounds g hg0 hupdate hfirst n

lemma bb2_matched_uniform_family_envelope (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (A : E →L[ℝ] E), A.toLinearMap.IsSymmetric →
      (∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧ inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2) →
      ∀ (g : ℕ → E), g 0 ≠ 0 →
      g 1 = operatorGradientStep A.toLinearMap (operatorBB2 A.toLinearMap (g 0)) (g 0) →
      (∀ n, g (n + 2) = operatorGradientStep A.toLinearMap (operatorBB2 A.toLinearMap (g n)) (g (n + 1))) →
      ∀ n, ‖g n‖ ≤ K * γ^n * ‖g 0‖ := by
  have hM : 0 ≤ 1 + b / a := by have hb := ha.trans_le hab; positivity
  obtain ⟨K, hK, henv⟩ := bb2_uniform_family_envelope a b γ (1 + b/a) ha hab hγ hM
  refine ⟨K, hK, ?_⟩
  intro E instN instI A hA hbounds g hg0 hfirst hupdate
  apply henv E A hA hbounds g hg0 hupdate
  rw [hfirst]
  exact matched_operator_bb2_first_bound A hA a b ha hab hbounds (g 0) hg0

lemma operator_bb2_normalized_rootFactor_le
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a * ‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b * ‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n + 2) = operatorGradientStep A.toLinearMap
      (operatorBB2 A.toLinearMap (g n)) (g (n + 1))) :
    rootFactor (fun n => ‖g n‖ / ‖g 0‖) ≤ rate a b := by
  have hn0 : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  let M := ‖g 1‖ / ‖g 0‖
  have hM : 0 ≤ M := div_nonneg (norm_nonneg _) hn0.le
  have hfirst : ‖g 1‖ ≤ M * ‖g 0‖ := by
    dsimp [M]
    rw [div_mul_cancel₀ _ hn0.ne']
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  obtain ⟨K, hK, henv⟩ := bb2_uniform_family_envelope a b γ M ha hab hγ hM
  apply rootFactor_le_of_envelope (fun n => ‖g n‖ / ‖g 0‖)
    (fun n => div_nonneg (norm_nonneg _) hn0.le) γ (hc0.trans hγ.le)
  exact ⟨K, hK, fun n => (div_le_iff hn0).mpr (henv E A hA hbounds g hg0 hupdate hfirst n)⟩

end
end BB
