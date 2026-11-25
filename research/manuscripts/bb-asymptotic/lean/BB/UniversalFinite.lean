import BB.FiniteCompression
import BB.ErrorObjective

/-!
# Dimension-independent spectral estimates transfer to real Hilbert spaces

`UniformSpectralEnvelope` isolates a scalar finite-state assertion.  The
theorems here prove its transfer first to actual finite-dimensional operator
iterations, then to an arbitrary real inner-product space by exact finite
compression.  The scalar assertion is an explicit premise of these transfer
lemmas and must be proved before using them as unconditional rate theorems.
-/

namespace BB
noncomputable section
open Filter

def UniformSpectralEnvelope (a b γ C : ℝ) : Prop :=
  ∀ (d : ℕ) (lam : Fin d → ℝ), (∀ i, a ≤ lam i ∧ lam i ≤ b) →
    ∀ n χ, prefixProduct (stateGrowth lam) (spectralMap lam) n χ ≤ C * γ^n

section Diagonal
variable {ι : Type*} [Fintype ι]

theorem gradient_envelope_from_prefix (lam : ι → ℝ) (C γ M : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hprefix : ∀ n χ, prefixProduct (stateGrowth lam) (spectralMap lam) n χ ≤ C * γ^n)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1)))
    (hfirst : normDiag (g 1) ≤ M * normDiag (g 0)) (n : ℕ) :
    normDiag (g n) ≤ (1+C*M/γ)*γ^n*normDiag (g 0) := by
  classical
  let D : ℝ := C*M/γ
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hC.le hM) hγ.le
  change normDiag (g n) ≤ (1+D)*γ^n*normDiag (g 0)
  by_cases hn0 : n = 0
  · subst n
    simp only [pow_zero,mul_one]
    nlinarith [norm_diag_nonneg (g 0)]
  · by_cases hn : g n = 0
    · rw [hn]
      simp only [normDiag,energy,Pi.zero_apply,zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero,Real.sqrt_zero]
      exact mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hγ.le n)) (norm_diag_nonneg _)
    · have hgpre := gradient_positive_before_nonzero lam g hupdate hg0 n hn
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [gradient_orbit_norm_product_up_to lam g hupdate m hgpre]
      calc
        normDiag (g 1) * prefixProduct (stateGrowth lam) (spectralMap lam) m
            (normalizedPair (g 1) (g 0) (hgpre 1 (by omega)) (hgpre 0 (by omega))) ≤
            normDiag (g 1)*(C*γ^m) :=
          mul_le_mul_of_nonneg_left (hprefix m _) (norm_diag_nonneg _)
        _ ≤ (M*normDiag (g 0))*(C*γ^m) :=
          mul_le_mul_of_nonneg_right hfirst (mul_nonneg hC.le (pow_nonneg hγ.le m))
        _ = D*γ^(m+1)*normDiag (g 0) := by
          dsimp [D]
          rw [pow_succ]
          field_simp
          ring
        _ ≤ (1+D)*γ^(m+1)*normDiag (g 0) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hγ.le _))
            (norm_diag_nonneg _)

end Diagonal

section Finite
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem universal_finite_operator_envelope {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b C γ M : ℝ) (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hU : UniformSpectralEnvelope a b γ C)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (H x) ∧
      inner (𝕜 := ℝ) x (H x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1)))
    (hfirst : ‖g 1‖ ≤ M*‖g 0‖) (n : ℕ) :
    ‖g n‖ ≤ (1+C*M/γ)*γ^n*‖g 0‖ := by
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hefirst : normDiag (eigenCoordinates hH (g 1)) ≤
      M*normDiag (eigenCoordinates hH (g 0)) := by
    simpa only [eigen_coordinates_norm] using hfirst
  simpa only [eigen_coordinates_norm] using
    gradient_envelope_from_prefix (eigenValues hH) C γ M hC hγ hM
      (hU _ _ (eigenvalue_bounds hH a b hbounds))
      (fun k => eigenCoordinates hH (g k)) he0 (eigen_coordinates_delayed_orbit hH g hupdate)
      hefirst n

end Finite

section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem operator_norm_bounds_via_compression (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (x : E) :
    a*‖x‖ ≤ ‖A x‖ ∧ ‖A x‖ ≤ b*‖x‖ := by
  let g : ℕ → E := fun _ => x
  let V := trajectorySpace A g 0
  let v : V := ⟨x,gradient_mem_trajectorySpace A g 0 0 (by omega)⟩
  have hAv : A (v : E) ∈ V := image_mem_trajectorySpace A g 0 0 (by omega)
  have he : (operatorCompression A V v : E) = A x :=
    orthogonalProjection_eq_self_iff.mpr hAv
  have h := finite_operator_norm_bounds (compression_symmetric A hA V) a b ha hab
    (compression_bounds A V a b hbounds) v
  change a*‖x‖ ≤ ‖(operatorCompression A V v : E)‖ ∧
    ‖(operatorCompression A V v : E)‖ ≤ b*‖x‖ at h
  simpa only [he] using h

/-- The exact compression theorem transfers a common finite-dimensional
constant to every real inner-product space. -/
theorem operator_envelope_from_universal_finite (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b C γ M : ℝ)
    (hC : 0 < C) (hγ : 0 < γ) (hM : 0 ≤ M)
    (hU : UniformSpectralEnvelope a b γ C)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1)))
    (hfirst : ‖g 1‖ ≤ M*‖g 0‖) (n : ℕ) :
    ‖g n‖ ≤ (1+C*M/γ)*γ^n*‖g 0‖ := by
  let V := trajectorySpace A g n
  let v := compressedTrajectory A g n
  have hv0 : v 0 ≠ 0 := by
    intro hz
    exact hg0 (congrArg Subtype.val hz)
  have hvfirst : ‖v 1‖ ≤ M*‖v 0‖ := hfirst
  have h := universal_finite_operator_envelope (compression_symmetric A hA V)
    a b C γ M hC hγ hM hU (compression_bounds A V a b hbounds) v hv0
    (compressed_trajectory_update A g n) hvfirst n
  change ‖(compressedTrajectory A g n n : E)‖ ≤ (1+C*M/γ)*γ^n*‖g 0‖ at h
  rw [compressed_trajectory_matches A g n hupdate n le_rfl] at h
  exact h

theorem positive_operator_bb1_bounds (A : E →L[ℝ] E) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (x : E) (hx : x ≠ 0) :
    0 < operatorBB1 A.toLinearMap x ∧
      1/b ≤ operatorBB1 A.toLinearMap x ∧ operatorBB1 A.toLinearMap x ≤ 1/a := by
  have hn : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
  have hd : 0 < inner (𝕜 := ℝ) x (A x) := (mul_pos ha hn).trans_le (hbounds x).1
  change 0 < ‖x‖^2/inner (𝕜 := ℝ) x (A x) ∧
    1/b ≤ ‖x‖^2/inner (𝕜 := ℝ) x (A x) ∧ ‖x‖^2/inner (𝕜 := ℝ) x (A x) ≤ 1/a
  refine ⟨div_pos hn hd,?_,?_⟩
  · apply (div_le_div_iff hb hd).mpr
    nlinarith [(hbounds x).2]
  · apply (div_le_div_iff hd ha).mpr
    nlinarith [(hbounds x).1]

theorem matched_operator_first_bound (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (x : E) (hx : x ≠ 0) :
    ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap x) x‖ ≤
      (1+b/a)*‖x‖ := by
  obtain ⟨hp,_hl,hu⟩ := positive_operator_bb1_bounds A a b ha (ha.trans_le hab) hbounds x hx
  have hn := (operator_norm_bounds_via_compression A hA a b ha hab hbounds x).2
  unfold operatorGradientStep
  calc
    ‖x-operatorBB1 A.toLinearMap x • A x‖ ≤ ‖x‖+‖operatorBB1 A.toLinearMap x • A x‖ := norm_sub_le _ _
    _ = ‖x‖+operatorBB1 A.toLinearMap x*‖A x‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hp]
    _ ≤ ‖x‖+(1/a)*(b*‖x‖) := add_le_add_left (mul_le_mul hu hn (norm_nonneg _) (by positivity)) _
    _ = (1+b/a)*‖x‖ := by ring

end General
end
end BB
