import BB.LinearRates
import BB.WeightedRates

/-! # Error and objective root factors

Norm and objective comparisons are proved for the genuine diagonal quadratic.
The root-factor identities include the boundedness hypotheses needed by the
real-valued `Filter.limsup`; actual BB trajectories discharge those hypotheses.
-/

namespace BB
noncomputable section
open Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def diagonalGradient (lam e : ι → ℝ) (i : ι) : ℝ := lam i * e i
def diagonalObjective (lam e : ι → ℝ) : ℝ := weightedEnergy lam e / 2

theorem norm_diag_sq (v : ι → ℝ) : (normDiag v)^2 = energy v :=
  Real.sq_sqrt (energy_nonneg v)

theorem diagonal_gradient_norm_bounds (lam e : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    a * normDiag e ≤ normDiag (diagonalGradient lam e) ∧
      normDiag (diagonalGradient lam e) ≤ b * normDiag e := by
  have hb : 0 < b := ha.trans_le hab
  have hlo : ∀ i, a^2 ≤ (lam i)^2 := by
    intro i
    nlinarith [(hlam i).1]
  have hhi : ∀ i, (lam i)^2 ≤ b^2 := by
    intro i
    nlinarith [(hlam i).1,(hlam i).2]
  have hs : spectralScale (fun i => (lam i)^2) e = diagonalGradient lam e := by
    funext i
    simp only [spectralScale,diagonalGradient,Real.sqrt_sq (ha.le.trans (hlam i).1)]
  have h := spectral_scale_norm_bounds (fun i => (lam i)^2) e (a^2) (b^2)
    (sq_pos_of_pos ha) hlo hhi
  simpa only [hs,Real.sqrt_sq ha.le,Real.sqrt_sq hb.le] using h

theorem diagonal_objective_bounds (lam e : ι → ℝ) (a b : ℝ)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    (a/2) * (normDiag e)^2 ≤ diagonalObjective lam e ∧
      diagonalObjective lam e ≤ (b/2) * (normDiag e)^2 := by
  rw [norm_diag_sq]
  unfold diagonalObjective
  have hl := weighted_energy_lower lam e a (fun i => (hlam i).1)
  have hu := weighted_energy_upper lam e b (fun i => (hlam i).2)
  constructor <;> linarith

/-- Scalar comparison theorem used for both BB1 and all fixed positive weights. -/
theorem compared_error_objective_root_factors (g e q : ℕ → ℝ) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hg : ∀ n, 0 ≤ g n) (he : ∀ n, 0 ≤ e n) (hg0 : 0 < g 0)
    (hgrad : ∀ n, a * e n ≤ g n ∧ g n ≤ b * e n)
    (hobj : ∀ n, (a/2)*(e n)^2 ≤ q n ∧ q n ≤ (b/2)*(e n)^2)
    (hbounded : atTop.IsBoundedUnder (· ≤ ·) (rootTerm g)) :
    rootFactor (fun n => e n / e 0) = rootFactor (fun n => g n / g 0) ∧
    rootFactor (fun n => q n / q 0) = (rootFactor (fun n => g n / g 0))^2 := by
  have heg : ∀ n, e n ≤ a⁻¹ * g n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hgrad n).1 (inv_pos.mpr ha).le
    simpa only [← mul_assoc,inv_mul_cancel ha.ne',one_mul] using h
  have heb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm e) :=
    rootTerm_bounded_of_comparison e g he hg hbounded a⁻¹ (inv_pos.mpr ha)
      (eventually_of_forall heg)
  have heq : rootFactor e = rootFactor g :=
    rootFactor_eq_of_comparable e g he hg hbounded a⁻¹ b (inv_pos.mpr ha) hb
      (eventually_of_forall heg) (eventually_of_forall (fun n => (hgrad n).2))
  have he0 : 0 < e 0 := by nlinarith [(hgrad 0).2]
  have hq : ∀ n, 0 ≤ q n := by
    intro n
    exact (mul_nonneg (div_nonneg ha.le (by norm_num)) (sq_nonneg _)).trans (hobj n).1
  have hq0 : 0 < q 0 :=
    (mul_pos (div_pos ha (by norm_num)) (sq_pos_of_pos he0)).trans_le (hobj 0).1
  have he2b := rootTerm_pow_bounded e he heb 2
  have heqbound : ∀ n, (e n)^2 ≤ (2/a)*q n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hobj n).1
      (show 0 ≤ (2:ℝ)/a from (div_pos (by norm_num) ha).le)
    have hc : (2/a)*(a/2) = (1:ℝ) := by field_simp [ha.ne']
    simpa only [← mul_assoc,hc,one_mul] using h
  have hqeq : rootFactor q = rootFactor (fun n => (e n)^2) :=
    rootFactor_eq_of_comparable q (fun n => (e n)^2) hq (fun n => sq_nonneg _)
      he2b (b/2) (2/a) (div_pos hb (by norm_num)) (div_pos (by norm_num) ha)
      (eventually_of_forall (fun n => (hobj n).2)) (eventually_of_forall heqbound)
  have hqb : atTop.IsBoundedUnder (· ≤ ·) (rootTerm q) :=
    rootTerm_bounded_of_comparison q (fun n => (e n)^2) hq (fun n => sq_nonneg _)
      he2b (b/2) (div_pos hb (by norm_num))
      (eventually_of_forall (fun n => (hobj n).2))
  rw [rootFactor_div_const e he heb (e 0) he0,
    rootFactor_div_const g hg hbounded (g 0) hg0,
    rootFactor_div_const q hq hqb (q 0) hq0,hqeq,rootFactor_pow e he heb 2,heq]
  exact ⟨rfl,rfl⟩

theorem diagonal_error_objective_root_factors (lam : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (g e : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hgradient : ∀ n, g n = diagonalGradient lam (e n))
    (hbounded : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => normDiag (g n)))) :
    rootFactor (fun n => normDiag (e n) / normDiag (e 0)) =
      rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ∧
    rootFactor (fun n => diagonalObjective lam (e n) / diagonalObjective lam (e 0)) =
      (rootFactor (fun n => normDiag (g n) / normDiag (g 0)))^2 := by
  apply compared_error_objective_root_factors (fun n => normDiag (g n))
    (fun n => normDiag (e n)) (fun n => diagonalObjective lam (e n)) a b ha (ha.trans_le hab)
    (fun n => norm_diag_nonneg _) (fun n => norm_diag_nonneg _) (Real.sqrt_pos.mpr hg0)
    _ _ hbounded
  · intro n
    dsimp only
    rw [hgradient n]
    exact diagonal_gradient_norm_bounds lam (e n) a b ha hab hlam
  · exact fun n => diagonal_objective_bounds lam (e n) a b hlam

theorem bb1_error_objective_root_factors (lam : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (g e : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hgradient : ∀ n, g n = diagonalGradient lam (e n))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1))) :
    rootFactor (fun n => normDiag (e n) / normDiag (e 0)) =
      rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ∧
    rootFactor (fun n => diagonalObjective lam (e n) / diagonalObjective lam (e 0)) =
      (rootFactor (fun n => normDiag (g n) / normDiag (g 0)))^2 := by
  classical
  exact diagonal_error_objective_root_factors lam a b ha hab hlam g e hg0 hgradient
    (gradient_rootTerm_bounded lam a b ha hab hlam g hg0 hupdate)

theorem weighted_error_objective_root_factors (lam ψ : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hψ : ∀ i, 0 < ψ i)
    (g e : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hgradient : ∀ n, g n = diagonalGradient lam (e n))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n+1))) :
    rootFactor (fun n => normDiag (e n) / normDiag (e 0)) =
      rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ∧
    rootFactor (fun n => diagonalObjective lam (e n) / diagonalObjective lam (e 0)) =
      (rootFactor (fun n => normDiag (g n) / normDiag (g 0)))^2 := by
  classical
  exact diagonal_error_objective_root_factors lam a b ha hab hlam g e hg0 hgradient
    (weighted_gradient_rootTerm_bounded lam ψ a b ha hab hlam hψ g hg0 hupdate)

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def operatorObjective (H : E →ₗ[ℝ] E) (e : E) : ℝ := inner (𝕜 := ℝ) e (H e)/2

theorem finite_operator_norm_bounds {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ v : E, a * ‖v‖^2 ≤ inner (𝕜 := ℝ) v (H v) ∧
      inner (𝕜 := ℝ) v (H v) ≤ b * ‖v‖^2) (x : E) :
    a * ‖x‖ ≤ ‖H x‖ ∧ ‖H x‖ ≤ b * ‖x‖ := by
  have hcoord : eigenCoordinates hH (H x) =
      diagonalGradient (eigenValues hH) (eigenCoordinates hH x) := by
    funext i
    exact eigen_coordinates_apply hH x i
  have hn := diagonal_gradient_norm_bounds (eigenValues hH) (eigenCoordinates hH x)
    a b ha hab (eigenvalue_bounds hH a b hbounds)
  rw [← hcoord,eigen_coordinates_norm,eigen_coordinates_norm] at hn
  exact hn

theorem eigen_coordinates_objective {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (e : E) :
    diagonalObjective (eigenValues hH) (eigenCoordinates hH e) = operatorObjective H e := by
  unfold diagonalObjective operatorObjective weightedEnergy
  rw [eigen_coordinates_inner]

theorem operator_error_objective_root_factors {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ v : E, a * ‖v‖^2 ≤ inner (𝕜 := ℝ) v (H v) ∧
      inner (𝕜 := ℝ) v (H v) ≤ b * ‖v‖^2)
    (g e : ℕ → E) (hg0 : g 0 ≠ 0) (hgradient : ∀ n, g n = H (e n))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = rootFactor (fun n => ‖g n‖/‖g 0‖) ∧
    rootFactor (fun n => operatorObjective H (e n)/operatorObjective H (e 0)) =
      (rootFactor (fun n => ‖g n‖/‖g 0‖))^2 := by
  have he0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hcoord : ∀ n, eigenCoordinates hH (g n) =
      diagonalGradient (eigenValues hH) (eigenCoordinates hH (e n)) := by
    intro n
    funext i
    rw [hgradient n,eigen_coordinates_apply]
    rfl
  simpa only [eigen_coordinates_norm,eigen_coordinates_objective] using
    bb1_error_objective_root_factors (eigenValues hH) a b ha hab
      (eigenvalue_bounds hH a b hbounds) (fun n => eigenCoordinates hH (g n))
      (fun n => eigenCoordinates hH (e n)) he0 hcoord
      (eigen_coordinates_delayed_orbit hH g hupdate)

end Operator

end
end BB
