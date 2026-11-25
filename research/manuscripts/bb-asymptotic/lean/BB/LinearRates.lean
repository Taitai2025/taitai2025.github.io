import BB.LinearCoordinates
import BB.GradientRates
import BB.ActiveSupport
import BB.EndpointSpectrum

/-! # Sharp upper bounds for the actual finite-dimensional operator iteration -/

namespace BB
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem operator_active_rootFactor_le {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b α₀ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hactive : ∀ i, eigenCoordinates hH (g 0) i ≠ 0 →
      a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b)
    (hfirst : g 1 = operatorGradientStep H α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖ / ‖g 0‖) ≤ rate a b := by
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hefirst : eigenCoordinates hH (g 1) =
      gradientUpdate (eigenValues hH) α₀ (eigenCoordinates hH (g 0)) := by
    rw [hfirst,eigen_coordinates_update]
  simpa only [eigen_coordinates_norm] using
    gradient_active_rootFactor_le (eigenValues hH) a b α₀ ha hab
      (fun n => eigenCoordinates hH (g n)) he0 hactive hefirst
      (eigen_coordinates_delayed_orbit hH g hupdate)

theorem operator_normalized_rootFactor_le {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ v : E, a * ‖v‖^2 ≤ inner (𝕜 := ℝ) v (H v) ∧
      inner (𝕜 := ℝ) v (H v) ≤ b * ‖v‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖ / ‖g 0‖) ≤ rate a b := by
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have he := gradient_normalized_rootFactor_le (eigenValues hH) a b ha hab
    (eigenvalue_bounds hH a b hbounds) (fun n => eigenCoordinates hH (g n))
    he0 (eigen_coordinates_delayed_orbit hH g hupdate)
  simpa only [eigen_coordinates_norm] using he

theorem operator_uniform_envelope_of_first_bound {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (a b γ M : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ v : E, a * ‖v‖^2 ≤ inner (𝕜 := ℝ) v (H v) ∧
      inner (𝕜 := ℝ) v (H v) ≤ b * ‖v‖^2)
    (hγ : rate a b < γ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → E), g 0 ≠ 0 →
      (∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) →
      ‖g 1‖ ≤ M * ‖g 0‖ → ∀ n, ‖g n‖ ≤ K * γ^n * ‖g 0‖ := by
  obtain ⟨K,hK,henv⟩ := gradient_uniform_envelope_of_first_bound (eigenValues hH)
    a b γ M ha hab (eigenvalue_bounds hH a b hbounds) hγ hM
  refine ⟨K,hK,?_⟩
  intro g hg0 hupdate hfirst
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hefirst : normDiag (eigenCoordinates hH (g 1)) ≤
      M * normDiag (eigenCoordinates hH (g 0)) := by
    simpa only [eigen_coordinates_norm] using hfirst
  simpa only [eigen_coordinates_norm] using henv (fun n => eigenCoordinates hH (g n))
    he0 (eigen_coordinates_delayed_orbit hH g hupdate) hefirst

theorem operator_matched_uniform_envelope {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ v : E, a * ‖v‖^2 ≤ inner (𝕜 := ℝ) v (H v) ∧
      inner (𝕜 := ℝ) v (H v) ≤ b * ‖v‖^2)
    (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → E), g 0 ≠ 0 →
      g 1 = operatorGradientStep H (operatorBB1 H (g 0)) (g 0) →
      (∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) →
      ∀ n, ‖g n‖ ≤ K * γ^n * ‖g 0‖ := by
  obtain ⟨K,hK,henv⟩ := gradient_matched_uniform_envelope (eigenValues hH)
    a b γ ha hab (eigenvalue_bounds hH a b hbounds) hγ
  refine ⟨K,hK,?_⟩
  intro g hg0 hfirst hupdate
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hefirst : eigenCoordinates hH (g 1) =
      gradientUpdate (eigenValues hH) (diagonalBB1 (eigenValues hH)
        (eigenCoordinates hH (g 0))) (eigenCoordinates hH (g 0)) := by
    rw [hfirst,eigen_coordinates_update,eigen_coordinates_quotient]
  simpa only [eigen_coordinates_norm] using henv (fun n => eigenCoordinates hH (g n))
    he0 hefirst (eigen_coordinates_delayed_orbit hH g hupdate)

/-- Two distinct spectral values yield an actual matched operator trajectory
with the exact geometric norm and root factor. -/
theorem operator_endpoint_sharp {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E))
    (ha : 0 < eigenValues hH lo) (hab : eigenValues hH lo < eigenValues hH hi) :
    ∃ g : ℕ → E, g 0 ≠ 0 ∧
      g 1 = operatorGradientStep H (operatorBB1 H (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate (eigenValues hH lo) (eigenValues hH hi))^n * ‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖ / ‖g 0‖) = rate (eigenValues hH lo) (eigenValues hH hi) := by
  classical
  have hne : lo ≠ hi := by intro h; subst hi; exact (lt_irrefl _ hab)
  let v := endpointGradient (eigenValues hH) lo hi 1 1
  let g : ℕ → E := fun n => fromEigenCoordinates hH (v n)
  have hcoord : ∀ n, eigenCoordinates hH (g n) = v n :=
    fun n => eigen_coordinates_from hH (v n)
  have hn : ∀ n, ‖g n‖ = normDiag (v n) := by
    intro n
    rw [← eigen_coordinates_norm hH (g n),hcoord n]
  obtain ⟨he0,hfirst,hupdate,henv,hroot⟩ :=
    endpoint_gradient_is_sharp (eigenValues hH) lo hi hne 1 1 ha hab one_ne_zero rfl
  change 0 < energy (v 0) at he0
  change v 1 = gradientUpdate (eigenValues hH) (diagonalBB1 (eigenValues hH) (v 0)) (v 0) at hfirst
  refine ⟨g,?_,?_,?_,?_,?_⟩
  · intro hzero
    have hz : ‖g 0‖ = 0 := by rw [hzero,norm_zero]
    rw [hn 0] at hz
    exact (ne_of_gt (Real.sqrt_pos.mpr he0)) hz
  · apply eigen_coordinates_injective hH
    rw [eigen_coordinates_update,eigen_coordinates_quotient,hcoord 0,hcoord 1]
    exact hfirst
  · intro n
    apply eigen_coordinates_injective hH
    rw [eigen_coordinates_update,eigen_coordinates_quotient,hcoord n,hcoord (n+1),hcoord (n+2)]
    exact hupdate n
  · intro n
    rw [hn n,hn 0]
    exact henv n
  · simpa only [hn] using hroot

end
end BB
