import BB.ApproxEigen

/-!
# Exact operator and inverse norms at positive spectral endpoints

These identities connect the nonlinear source's endpoint notation to actual
continuous operators.  The inverse is constructed by coercivity, while the
equalities use genuine approximate endpoint eigenvectors.
-/

noncomputable section
namespace BB
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem positive_operator_norm_eq_upper_endpoint (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (hbspec : b ∈ spectrum ℝ A) :
    ‖A‖ = b := by
  apply le_antisymm
  · exact A.opNorm_le_bound (ha.le.trans hab)
      (fun x => (operator_norm_bounds_via_compression A hA a b ha hab hbounds x).2)
  · by_contra hn
    have _hlt : ‖A‖ < b := lt_of_not_ge hn
    obtain ⟨x,hx,hRay⟩ := spectrum_upper_rayleigh A b ((b-‖A‖)/2) hbspec (by linarith)
    have hi : inner (𝕜 := ℝ) x (A x) ≤ ‖A‖ := by
      calc
        _ ≤ ‖x‖ * ‖A x‖ := real_inner_le_norm _ _
        _ ≤ ‖x‖ * (‖A‖ * ‖x‖) := mul_le_mul_of_nonneg_left (A.le_opNorm x) (norm_nonneg x)
        _ = ‖A‖ := by rw [hx]; ring
    linarith

theorem positive_inverse_norm_eq_lower_endpoint (A B : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hBA : B * A = 1) (hAB : A * B = 1) :
    ‖B‖ = a⁻¹ := by
  have hBAx (x : E) : B (A x) = x := congrArg (fun T : E →L[ℝ] E => T x) hBA
  have hABx (x : E) : A (B x) = x := congrArg (fun T : E →L[ℝ] E => T x) hAB
  apply le_antisymm
  · apply B.opNorm_le_bound (inv_nonneg.mpr ha.le)
    intro x
    have h := (operator_norm_bounds_via_compression A hA a b ha hab hbounds (B x)).1
    rw [hABx] at h
    have hi := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr ha.le)
    simpa only [← mul_assoc, inv_mul_cancel ha.ne', one_mul] using hi
  · by_contra hn
    have hlt : ‖B‖ < a⁻¹ := lt_of_not_ge hn
    have hgap : 0 < 1 - ‖B‖ * a := by
      have h := mul_lt_mul_of_pos_right hlt ha
      rw [inv_mul_cancel ha.ne'] at h
      linarith
    let δ := (1 - ‖B‖ * a) / (2 * (‖B‖ + 1))
    have hd : 0 < δ := div_pos hgap (by positivity)
    have heq : (2 * (‖B‖ + 1)) * δ = 1 - ‖B‖ * a := by
      dsimp [δ]
      exact mul_div_cancel₀ _ (by positivity)
    obtain ⟨x,hx,hres⟩ := spectrum_approximate_lower A hA a b hab hbounds haspec δ hd
    have hAx : ‖A x‖ < a + δ := by
      calc
        _ ≤ ‖A x-a • x‖ + ‖a • x‖ := by
          calc
            ‖A x‖ = ‖(A x-a • x)+a • x‖ := by rw [sub_add_cancel]
            _ ≤ _ := norm_add_le _ _
        _ = ‖A x-a • x‖ + a := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, hx, mul_one]
        _ < a + δ := by linarith
    have hi : 1 ≤ ‖B‖ * ‖A x‖ := by
      calc
        1 = ‖B (A x)‖ := by rw [hBAx, hx]
        _ ≤ ‖B‖ * ‖A x‖ := B.le_opNorm (A x)
    have hm := mul_le_mul_of_nonneg_left hAx.le (norm_nonneg B)
    nlinarith [norm_nonneg B]

theorem positive_operator_exact_inverse_exists (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    ∃ B : E →L[ℝ] E, B*A = 1 ∧ A*B = 1 ∧ ‖B‖⁻¹ = a ∧ ‖A‖ = b := by
  obtain ⟨U,hU⟩ := coercive_operator_isUnit A a ha (fun x => (hbounds x).1)
  let B : E →L[ℝ] E := ↑(U⁻¹)
  have hBA : B*A = 1 := by rw [← hU]; exact U.inv_val
  have hAB : A*B = 1 := by rw [← hU]; exact U.val_inv
  refine ⟨B,hBA,hAB,?_,positive_operator_norm_eq_upper_endpoint A hA a b ha hab hbounds hbspec⟩
  rw [positive_inverse_norm_eq_lower_endpoint A B hA a b ha hab hbounds haspec hBA hAB, inv_inv]

end BB
