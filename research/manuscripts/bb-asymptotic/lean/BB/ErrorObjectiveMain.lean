import BB.FiniteOperatorMain
import BB.ErrorObjective

/-!
# Attained sharp error and objective factors

These sets quantify over actual operator trajectories and the corresponding
error vectors `gₙ = H eₙ`. Their maxima are assembled explicitly, rather than
left as an informal consequence of norm comparisons.
-/

namespace BB
noncomputable section
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def affineQuadratic (H : E →ₗ[ℝ] E) (b x : E) : ℝ :=
  inner (𝕜 := ℝ) x (H x)/2-inner (𝕜 := ℝ) b x

/-- Translating a stationary point turns the actual affine quadratic objective
gap into the positive quadratic form used in the rate statements. -/
theorem affine_quadratic_gap (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    (b xstar x : E) (hstationary : H xstar = b) :
    affineQuadratic H b x-affineQuadratic H b xstar = operatorObjective H (x-xstar) := by
  subst b
  simp only [affineQuadratic,operatorObjective,map_sub,inner_sub_left,inner_sub_right]
  linarith [hH xstar x,real_inner_comm x (H xstar),real_inner_comm xstar (H xstar)]

lemma affine_gradient_translation (H : E →ₗ[ℝ] E) (b xstar x : E)
    (hstationary : H xstar = b) : H x-b = H (x-xstar) := by
  rw [map_sub,hstationary]

def operatorErrorFactors (H : E →ₗ[ℝ] E) (step : E → ℝ) : Set ℝ :=
  {ρ | ∃ (g e : ℕ → E) (α₀ : ℝ), IsOperatorDelayedTrajectory H step g α₀ ∧
    (∀ n, g n = H (e n)) ∧ rootFactor (fun n => ‖e n‖/‖e 0‖) = ρ}

def operatorObjectiveFactors (H : E →ₗ[ℝ] E) (step : E → ℝ) : Set ℝ :=
  {ρ | ∃ (g e : ℕ → E) (α₀ : ℝ), IsOperatorDelayedTrajectory H step g α₀ ∧
    (∀ n, g n = H (e n)) ∧
    rootFactor (fun n => operatorObjective H (e n)/operatorObjective H (e 0)) = ρ}

lemma operator_error_factor_set_eq (H : E →ₗ[ℝ] E) (step : E → ℝ)
    (errorOf : E → E) (herror : ∀ x, H (errorOf x) = x)
    (hidentity : ∀ (g e : ℕ → E) (α₀ : ℝ), IsOperatorDelayedTrajectory H step g α₀ →
      (∀ n, g n = H (e n)) → rootFactor (fun n => ‖e n‖/‖e 0‖) = operatorTrajectoryFactor g) :
    operatorErrorFactors H step = operatorAttainableFactors H step := by
  ext ρ
  constructor
  · rintro ⟨g,e,α₀,hg,he,hρ⟩
    exact ⟨g,α₀,hg,(hidentity g e α₀ hg he).symm.trans hρ⟩
  · rintro ⟨g,α₀,hg,hρ⟩
    exact ⟨g,fun n => errorOf (g n),α₀,hg,fun n => (herror (g n)).symm,
      (hidentity g (fun n => errorOf (g n)) α₀ hg (fun n => (herror (g n)).symm)).trans hρ⟩

lemma operator_objective_factor_set_eq (H : E →ₗ[ℝ] E) (step : E → ℝ)
    (errorOf : E → E) (herror : ∀ x, H (errorOf x) = x)
    (hidentity : ∀ (g e : ℕ → E) (α₀ : ℝ), IsOperatorDelayedTrajectory H step g α₀ →
      (∀ n, g n = H (e n)) →
      rootFactor (fun n => operatorObjective H (e n)/operatorObjective H (e 0)) =
        (operatorTrajectoryFactor g)^2) :
    operatorObjectiveFactors H step = (fun r : ℝ => r^2) '' operatorAttainableFactors H step := by
  ext ρ
  constructor
  · rintro ⟨g,e,α₀,hg,he,hρ⟩
    exact ⟨operatorTrajectoryFactor g,⟨g,α₀,hg,rfl⟩,(hidentity g e α₀ hg he).symm.trans hρ⟩
  · rintro ⟨r,⟨g,α₀,hg,hr⟩,rfl⟩
    refine ⟨g,fun n => errorOf (g n),α₀,hg,fun n => (herror (g n)).symm,?_⟩
    rw [hidentity g _ α₀ hg (fun n => (herror (g n)).symm),hr]

lemma isGreatest_square_image (s : Set ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hmax : IsGreatest s c) (hnonneg : ∀ r ∈ s, 0 ≤ r) :
    IsGreatest ((fun r : ℝ => r^2) '' s) (c^2) := by
  refine ⟨⟨c,hmax.1,rfl⟩,?_⟩
  rintro _ ⟨r,hr,rfl⟩
  change r^2 ≤ c^2
  have h := hmax.2 hr
  have h0 := hnonneg r hr
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (add_nonneg hc h0)]

section Finite
variable [FiniteDimensional ℝ E]

def finiteOperatorError {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : E) : E :=
  fromEigenCoordinates hH (fun i => eigenCoordinates hH g i / eigenValues hH i)

lemma finite_operator_error_inverse {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hlam : ∀ i, eigenValues hH i ≠ 0) (g : E) : H (finiteOperatorError hH g) = g := by
  apply eigen_coordinates_injective hH
  funext i
  rw [eigen_coordinates_apply]
  change eigenValues hH i * eigenCoordinates hH (fromEigenCoordinates hH _) i = _
  rw [eigen_coordinates_from]
  exact mul_div_cancel₀ _ (hlam i)

theorem finite_weighted_operator_error_objective_factors {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i)
    (g e : ℕ → E) (α₀ : ℝ)
    (hg : IsOperatorDelayedTrajectory H (operatorWeightedBB H (finiteSpectralWeight hH ψ)) g α₀)
    (he : ∀ n, g n = H (e n)) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = operatorTrajectoryFactor g ∧
    rootFactor (fun n => operatorObjective H (e n)/operatorObjective H (e 0)) =
      (operatorTrajectoryFactor g)^2 := by
  have hv := operator_trajectory_coordinates hH _ _ (eigen_coordinates_weighted_quotient hH ψ) g α₀ hg
  have hec : ∀ n, eigenCoordinates hH (g n) =
      diagonalGradient (eigenValues hH) (eigenCoordinates hH (e n)) := by
    intro n
    funext i
    rw [he n,eigen_coordinates_apply]
    rfl
  simpa only [eigen_coordinates_norm,eigen_coordinates_objective,operatorTrajectoryFactor] using
    weighted_error_objective_root_factors (eigenValues hH) ψ a b ha hab hlam hψ
      (fun n => eigenCoordinates hH (g n)) (fun n => eigenCoordinates hH (e n))
      hv.initial_pos hec hv.update

lemma finite_weighted_operator_factor_nonneg {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i)
    (g : ℕ → E) (α₀ : ℝ)
    (hg : IsOperatorDelayedTrajectory H (operatorWeightedBB H (finiteSpectralWeight hH ψ)) g α₀) :
    0 ≤ operatorTrajectoryFactor g := by
  have hv := operator_trajectory_coordinates hH _ _ (eigen_coordinates_weighted_quotient hH ψ) g α₀ hg
  have hb := weighted_gradient_rootTerm_bounded (eigenValues hH) ψ a b ha hab hlam hψ
    (fun n => eigenCoordinates hH (g n)) hv.initial_pos hv.update
  rw [← operator_factor_coordinates hH]
  unfold normalizedTrajectoryFactor
  change 0 ≤ rootFactor (fun n => normDiag (eigenCoordinates hH (g n)) /
    normDiag (eigenCoordinates hH (g 0)))
  have hn : 0 < normDiag (eigenCoordinates hH (g 0)) := Real.sqrt_pos.mpr hv.initial_pos
  rw [rootFactor_div_const _ (fun n => norm_diag_nonneg _) hb _ hn]
  exact rootFactor_nonneg _ (fun n => norm_diag_nonneg _) hb

theorem finite_weighted_operator_error_objective_isGreatest {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    IsGreatest (operatorErrorFactors H (operatorWeightedBB H (finiteSpectralWeight hH ψ))) (rate a b) ∧
      IsGreatest (operatorObjectiveFactors H (operatorWeightedBB H (finiteSpectralWeight hH ψ)))
        ((rate a b)^2) := by
  have hmax := finite_operator_weighted_isGreatest hH ψ lo hi a b ha hab hlo hhi hlam hψ
  have herr := finite_operator_error_inverse hH (fun i => (ha.trans_le (hlam i).1).ne')
  have heq := operator_error_factor_set_eq H (operatorWeightedBB H (finiteSpectralWeight hH ψ))
    (finiteOperatorError hH) herr
    (fun g e α₀ hg he => (finite_weighted_operator_error_objective_factors hH ψ a b ha hab hlam hψ g e α₀ hg he).1)
  have hobj := operator_objective_factor_set_eq H (operatorWeightedBB H (finiteSpectralWeight hH ψ))
    (finiteOperatorError hH) herr
    (fun g e α₀ hg he => (finite_weighted_operator_error_objective_factors hH ψ a b ha hab hlam hψ g e α₀ hg he).2)
  rw [heq,hobj]
  refine ⟨hmax,isGreatest_square_image _ _ (div_nonneg (sub_nonneg.mpr hab) (by linarith)) hmax ?_⟩
  rintro r ⟨g,α₀,hg,rfl⟩
  exact finite_weighted_operator_factor_nonneg hH ψ a b ha hab hlam hψ g α₀ hg

theorem finite_weighted_operator_error_objective_suprema {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    sSup (operatorErrorFactors H (operatorWeightedBB H (finiteSpectralWeight hH ψ))) = rate a b ∧
      sSup (operatorObjectiveFactors H (operatorWeightedBB H (finiteSpectralWeight hH ψ))) =
        (rate a b)^2 := by
  have h := finite_weighted_operator_error_objective_isGreatest hH ψ lo hi a b ha hab hlo hhi hlam hψ
  exact ⟨h.1.csSup_eq,h.2.csSup_eq⟩

/-- One actual matched sequence simultaneously attains the gradient, error,
and objective factors, including the singleton-spectrum case. -/
theorem finite_weighted_operator_error_objective_matched_attainment {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    ∃ g e : ℕ → E,
      IsOperatorDelayedTrajectory H (operatorWeightedBB H (finiteSpectralWeight hH ψ)) g
        (operatorWeightedBB H (finiteSpectralWeight hH ψ) (g 0)) ∧
      (∀ n, g n = H (e n)) ∧ operatorTrajectoryFactor g = rate a b ∧
      rootFactor (fun n => ‖e n‖/‖e 0‖) = rate a b ∧
      rootFactor (fun n => operatorObjective H (e n)/operatorObjective H (e 0)) = (rate a b)^2 := by
  obtain ⟨v,hv,hr⟩ := weighted_matched_factor_attained (eigenValues hH) ψ lo hi a b ha hab hlo hhi hψ
  let g : ℕ → E := fun n => fromEigenCoordinates hH (v n)
  let e : ℕ → E := fun n => finiteOperatorError hH (g n)
  have hg := diagonal_trajectory_from_coordinates hH _ _ (eigen_coordinates_weighted_quotient hH ψ) v _ hv
  have hs : operatorWeightedBB H (finiteSpectralWeight hH ψ) (g 0) =
      weightedBB (eigenValues hH) ψ (v 0) := by
    rw [eigen_coordinates_weighted_quotient]
    change weightedBB (eigenValues hH) ψ (eigenCoordinates hH (fromEigenCoordinates hH (v 0))) = _
    rw [eigen_coordinates_from]
  change IsOperatorDelayedTrajectory H (operatorWeightedBB H (finiteSpectralWeight hH ψ)) g _ at hg
  rw [← hs] at hg
  have he : ∀ n, g n = H (e n) := fun n =>
    (finite_operator_error_inverse hH (fun i => (ha.trans_le (hlam i).1).ne') (g n)).symm
  have hgρ : operatorTrajectoryFactor g = rate a b := (operator_factor_from_coordinates hH v).trans hr
  have hid := finite_weighted_operator_error_objective_factors hH ψ a b ha hab hlam hψ g e _ hg he
  rw [hgρ] at hid
  exact ⟨g,e,hg,he,hgρ,hid⟩

lemma finite_weighted_one_step_eq_bb1 {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) :
    operatorWeightedBB H (finiteSpectralWeight hH (fun _ => 1)) = operatorBB1 H := by
  funext x
  rw [eigen_coordinates_weighted_quotient,weighted_bb_one,← eigen_coordinates_quotient]

theorem finite_bb1_operator_error_objective_isGreatest {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    IsGreatest (operatorErrorFactors H (operatorBB1 H)) (rate a b) ∧
      IsGreatest (operatorObjectiveFactors H (operatorBB1 H)) ((rate a b)^2) := by
  simpa only [finite_weighted_one_step_eq_bb1] using
    finite_weighted_operator_error_objective_isGreatest hH (fun _ => 1) lo hi a b ha hab hlo hhi hlam
      (fun _ => zero_lt_one)

theorem finite_bb1_operator_error_objective_suprema {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    sSup (operatorErrorFactors H (operatorBB1 H)) = rate a b ∧
      sSup (operatorObjectiveFactors H (operatorBB1 H)) = (rate a b)^2 := by
  have h := finite_bb1_operator_error_objective_isGreatest hH lo hi a b ha hab hlo hhi hlam
  exact ⟨h.1.csSup_eq,h.2.csSup_eq⟩

theorem finite_bb1_operator_error_objective_matched_attainment {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hlam : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    ∃ g e : ℕ → E, IsOperatorDelayedTrajectory H (operatorBB1 H) g (operatorBB1 H (g 0)) ∧
      (∀ n, g n = H (e n)) ∧ operatorTrajectoryFactor g = rate a b ∧
      rootFactor (fun n => ‖e n‖/‖e 0‖) = rate a b ∧
      rootFactor (fun n => operatorObjective H (e n)/operatorObjective H (e 0)) = (rate a b)^2 := by
  simpa only [finite_weighted_one_step_eq_bb1] using
    finite_weighted_operator_error_objective_matched_attainment hH (fun _ => 1) lo hi a b ha hab hlo hhi hlam
      (fun _ => zero_lt_one)

end Finite
end
end BB
