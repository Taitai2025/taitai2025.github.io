import BB.FiniteOperatorMain
import BB.HilbertRates
import BB.HilbertActive

/-!
# Exact attainment for every balanced endpoint initial vector

Determinism transfers the explicit endpoint orbit to any actual trajectory
with the same balanced initial gradient. The final statements also assemble
the actual fixed-operator supremum when both extreme spectral values are
eigenvalues.
-/

namespace BB
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem single_eigenvalue_matched_terminates (H : E →ₗ[ℝ] E) (ell : ℝ) (hell : 0 < ell)
    (x : E) (hx : x ≠ 0) (heigen : H x = ell • x) :
    operatorGradientStep H (operatorBB1 H x) x = 0 := by
  rw [eigenvector_bb1_quotient H ell hell x hx heigen]
  simp only [operatorGradientStep,heigen,smul_smul,one_div_mul_cancel hell.ne',one_smul,sub_self]

theorem balanced_endpoint_trajectory_exact (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (hp0 : p ≠ 0) (hbalance : ‖p‖ = ‖q‖)
    (g : ℕ → E) (h0 : g 0 = p+q)
    (hfirst : g 1 = operatorGradientStep H (operatorBB1 H (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧ operatorTrajectoryFactor g = rate a b := by
  obtain ⟨_hg0,_hα,hvfirst,hvupdate,hvnorm,hvroot⟩ :=
    hilbert_endpoint_matched_orbit H hH a b ha hab p q hp hq hp0 hbalance
  have hzero : g 0 = hilbertEndpointOrbit a b p q 0 := by
    simpa only [hilbertEndpointOrbit,pow_zero,one_smul] using h0
  have hone : g 1 = hilbertEndpointOrbit a b p q 1 := by rw [hfirst,hzero,← hvfirst]
  have he := operator_delayed_trajectory_unique H (operatorBB1 H) g (hilbertEndpointOrbit a b p q)
    hzero hone hupdate hvupdate
  rw [he]
  exact ⟨hvnorm,hvroot⟩

theorem weighted_balanced_endpoint_trajectory_exact (H W : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (a b wa wb : ℝ) (ha : 0 < a) (hab : a < b) (hwa : 0 < wa) (p q : E)
    (hp : H p = a • p) (hq : H q = b • q) (hwp : W p = wa • p) (hwq : W q = wb • q)
    (hp0 : p ≠ 0) (hbalance : wa*‖p‖^2=wb*‖q‖^2)
    (g : ℕ → E) (h0 : g 0 = p+q)
    (hfirst : g 1 = operatorGradientStep H (operatorWeightedBB H W (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorWeightedBB H W (g n)) (g (n+1))) :
    (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧ operatorTrajectoryFactor g = rate a b := by
  obtain ⟨_hg0,_hα,hvfirst,hvupdate,hvnorm,hvroot⟩ :=
    hilbert_weighted_endpoint_matched_orbit H W hH a b wa wb ha hab hwa p q hp hq hwp hwq hp0 hbalance
  have hzero : g 0 = hilbertEndpointOrbit a b p q 0 := by
    simpa only [hilbertEndpointOrbit,pow_zero,one_smul] using h0
  have hone : g 1 = hilbertEndpointOrbit a b p q 1 := by rw [hfirst,hzero,← hvfirst]
  have he := operator_delayed_trajectory_unique H (operatorWeightedBB H W) g (hilbertEndpointOrbit a b p q)
    hzero hone hupdate hvupdate
  rw [he]
  exact ⟨hvnorm,hvroot⟩

section Finite
variable [FiniteDimensional ℝ E]

theorem finite_spectral_weight_eigenvector {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (Ψ : ℝ → ℝ) (ell : ℝ) (x : E) (hx : H x = ell • x) :
    finiteSpectralWeight hH (fun i => Ψ (eigenValues hH i)) x = Ψ ell • x := by
  apply eigen_coordinates_injective hH
  funext i
  rw [eigen_coordinates_spectral_weight,eigen_coordinates_smul]
  change Ψ (eigenValues hH i)*eigenCoordinates hH x i = Ψ ell*eigenCoordinates hH x i
  by_cases hi : eigenCoordinates hH x i = 0
  · simp only [hi,mul_zero]
  · have he := congrArg (fun y => eigenCoordinates hH y i) hx
    change eigenCoordinates hH (H x) i = eigenCoordinates hH (ell • x) i at he
    rw [eigen_coordinates_apply,eigen_coordinates_smul] at he
    have hei : eigenValues hH i = ell := mul_right_cancel₀ hi he
    rw [hei]

theorem finite_weighted_balanced_endpoint_exact {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (Ψ : ℝ → ℝ) (a b : ℝ) (ha : 0 < a) (hab : a < b) (hΨa : 0 < Ψ a)
    (p q : E) (hp : H p = a • p) (hq : H q = b • q)
    (hp0 : p ≠ 0) (hbalance : Ψ a*‖p‖^2=Ψ b*‖q‖^2)
    (g : ℕ → E) (h0 : g 0 = p+q)
    (hfirst : g 1 = operatorGradientStep H
      (operatorWeightedBB H (finiteSpectralWeight hH (fun i => Ψ (eigenValues hH i))) (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H
      (operatorWeightedBB H (finiteSpectralWeight hH (fun i => Ψ (eigenValues hH i))) (g n)) (g (n+1))) :
    (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧ operatorTrajectoryFactor g = rate a b :=
  weighted_balanced_endpoint_trajectory_exact H _ hH a b (Ψ a) (Ψ b) ha hab hΨa p q hp hq
    (finite_spectral_weight_eigenvector hH Ψ a p hp)
    (finite_spectral_weight_eigenvector hH Ψ b q hq) hp0 hbalance g h0 hfirst hupdate

end Finite

theorem hilbert_endpoint_isGreatest (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (hep : ∃ p : E, p ≠ 0 ∧ A p = a • p)
    (heq : ∃ q : E, q ≠ 0 ∧ A q = b • q) :
    IsGreatest (operatorAttainableFactors A.toLinearMap (operatorBB1 A.toLinearMap)) (rate a b) := by
  obtain ⟨g,hg0,hα,hfirst,hupdate,_hnorm,hroot⟩ :=
    hilbert_endpoint_eigenvalues_attain A.toLinearMap hA a b ha hab hep heq
  refine ⟨⟨g,operatorBB1 A.toLinearMap (g 0),⟨hg0,hα,hfirst,hupdate⟩,hroot⟩,?_⟩
  rintro r ⟨v,α₀,hv,rfl⟩
  exact hilbert_normalized_rootFactor_le A hA a b ha hab.le hbounds v hv.initial_ne hv.update

theorem hilbert_endpoint_supremum (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (hep : ∃ p : E, p ≠ 0 ∧ A p = a • p)
    (heq : ∃ q : E, q ≠ 0 ∧ A q = b • q) :
    sSup (operatorAttainableFactors A.toLinearMap (operatorBB1 A.toLinearMap)) = rate a b :=
  (hilbert_endpoint_isGreatest A hA a b ha hab hbounds hep heq).csSup_eq

end
end BB
