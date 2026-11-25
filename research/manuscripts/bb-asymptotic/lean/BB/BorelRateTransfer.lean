import BB.HilbertConjugacy
import BB.HilbertUniformThresholds

/-!
# Exact two-way transfer of matched uniform rate sets

A boundedly invertible commuting square-root conjugacy transports every actual
matched trajectory in both directions. Therefore the admissible rate sets,
including their positive prefactors, coincide exactly.
-/

noncomputable section
namespace BB

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (A W S : E →L[ℝ] E) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : W = S.comp S) (hcomm : ∀ x, S (A x) = A (S x))
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (hlower : ∀ x, s * ‖x‖ ≤ ‖S x‖) (hupper : ∀ x, ‖S x‖ ≤ t * ‖x‖)

lemma norm_lower_operator_injective : Function.Injective S := by
  intro x y hxy
  by_contra h
  have hn := norm_lower_operator_ne_zero S s hs hlower (x-y) (sub_ne_zero.mpr h)
  apply hn
  rw [map_sub, hxy, sub_self]

lemma conjugate_matched_trajectory (g : ℕ → E)
    (hg : IsOperatorDelayedTrajectory A.toLinearMap (operatorWeightedBB A.toLinearMap W.toLinearMap)
      g (operatorWeightedBB A.toLinearMap W.toLinearMap (g 0))) :
    IsOperatorDelayedTrajectory A.toLinearMap (operatorBB1 A.toLinearMap)
      (fun n => S (g n)) (operatorBB1 A.toLinearMap (S (g 0))) := by
  refine ⟨norm_lower_operator_ne_zero S s hs hlower (g 0) hg.initial_ne, ?_, ?_, ?_⟩
  · rw [← operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
    exact hg.firstStep_pos
  · rw [hg.first, commuting_operator_step A S hcomm,
      operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
  · exact operator_weighted_orbit_conjugacy A W S hS hsquare hcomm g hg.update

lemma matched_trajectory_of_conjugate (g : ℕ → E)
    (hg : IsOperatorDelayedTrajectory A.toLinearMap (operatorBB1 A.toLinearMap)
      (fun n => S (g n)) (operatorBB1 A.toLinearMap (S (g 0)))) :
    IsOperatorDelayedTrajectory A.toLinearMap (operatorWeightedBB A.toLinearMap W.toLinearMap)
      g (operatorWeightedBB A.toLinearMap W.toLinearMap (g 0)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hzero
    apply hg.initial_ne
    rw [hzero, map_zero]
  · rw [operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
    exact hg.firstStep_pos
  · apply norm_lower_operator_injective S s hs hlower
    rw [commuting_operator_step A S hcomm, operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
    exact hg.first
  · intro n
    apply norm_lower_operator_injective S s hs hlower
    rw [commuting_operator_step A S hcomm, operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
    exact hg.update n

/-- Both directions preserve the admissible rate γ, multiplying only its prefactor. -/
theorem weighted_matched_uniform_rates_eq (hunit : IsUnit S) :
    operatorMatchedUniformRates A.toLinearMap (operatorWeightedBB A.toLinearMap W.toLinearMap) =
      operatorMatchedUniformRates A.toLinearMap (operatorBB1 A.toLinearMap) := by
  ext γ
  constructor
  · rintro ⟨hγ0, hγ1, C, hC, henv⟩
    refine ⟨hγ0, hγ1, (t/s)*C, mul_pos (div_pos ht hs) hC, ?_⟩
    intro v hv n
    obtain ⟨U, hU⟩ := hunit
    let g : ℕ → E := fun k => (↑(U⁻¹) : E →L[ℝ] E) (v k)
    have hSv : ∀ k, S (g k) = v k := by
      intro k
      rw [← hU]
      exact congrArg (fun T : E →L[ℝ] E => T (v k)) U.val_inv
    have hgS : IsOperatorDelayedTrajectory A.toLinearMap (operatorBB1 A.toLinearMap)
        (fun k => S (g k)) (operatorBB1 A.toLinearMap (S (g 0))) := by
      simpa only [hSv] using hv
    have hg := matched_trajectory_of_conjugate A W S hS hsquare hcomm s hs hlower g hgS
    have he := henv g hg n
    have h0 : ‖g 0‖ ≤ s⁻¹ * ‖v 0‖ := by
      have h := mul_le_mul_of_nonneg_left (hlower (g 0)) (inv_pos.mpr hs).le
      simpa only [← mul_assoc, inv_mul_cancel hs.ne', one_mul, hSv] using h
    calc
      ‖v n‖ = ‖S (g n)‖ := by rw [hSv]
      _ ≤ t * ‖g n‖ := hupper (g n)
      _ ≤ t * (C * γ^n * ‖g 0‖) := mul_le_mul_of_nonneg_left he ht.le
      _ ≤ t * (C * γ^n * (s⁻¹ * ‖v 0‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left h0 (mul_nonneg hC.le (pow_nonneg hγ0.le n))) ht.le
      _ = (t/s) * C * γ^n * ‖v 0‖ := by ring
  · rintro ⟨hγ0, hγ1, C, hC, henv⟩
    refine ⟨hγ0, hγ1, (t/s)*C, mul_pos (div_pos ht hs) hC, ?_⟩
    intro g hg n
    have hv := conjugate_matched_trajectory A W S hS hsquare hcomm s hs hlower g hg
    have he := henv (fun k => S (g k)) hv n
    have hn : ‖g n‖ ≤ s⁻¹ * ‖S (g n)‖ := by
      have h := mul_le_mul_of_nonneg_left (hlower (g n)) (inv_pos.mpr hs).le
      simpa only [← mul_assoc, inv_mul_cancel hs.ne', one_mul] using h
    calc
      ‖g n‖ ≤ s⁻¹ * ‖S (g n)‖ := hn
      _ ≤ s⁻¹ * (C * γ^n * ‖S (g 0)‖) := mul_le_mul_of_nonneg_left he (inv_pos.mpr hs).le
      _ ≤ s⁻¹ * (C * γ^n * (t * ‖g 0‖)) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hupper (g 0)) (mul_nonneg hC.le (pow_nonneg hγ0.le n)))
        (inv_pos.mpr hs).le
      _ = (t/s) * C * γ^n * ‖g 0‖ := by ring

end BB
