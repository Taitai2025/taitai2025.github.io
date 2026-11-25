import BB.OperatorCondition
import BB.SortedOperator

set_option autoImplicit false

noncomputable section
namespace BB.Operator
open Module.End
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- A bound on diagonal spectral multipliers gives the genuine Hilbert-space norm bound. -/
theorem coordinate_multiplier_norm_bound {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (γ : Eigenvalues H → ℝ) {M : ℝ} (hM : 0 ≤ M) {x y : V}
    (hcoords : ∀ μ, coordinates hH y μ = γ μ • coordinates hH x μ)
    (hγ : ∀ μ, |γ μ| ≤ M) : ‖y‖ ≤ M*‖x‖ := by
  have hsq : ‖y‖^2 ≤ M^2*‖x‖^2 := by
    calc
      ‖y‖^2 = ∑ μ, ‖coordinates hH y μ‖^2 := (coordinates_sq_norm hH y).symm
      _ ≤ ∑ μ, M^2*‖coordinates hH x μ‖^2 := by
        apply Finset.sum_le_sum
        intro μ _
        rw [hcoords μ,norm_smul,Real.norm_eq_abs,mul_pow]
        have hh : |γ μ|^2 ≤ M^2 := by nlinarith only [hγ μ,abs_nonneg (γ μ),hM]
        exact mul_le_mul_of_nonneg_right hh (sq_nonneg _)
      _ = M^2*‖x‖^2 := by rw [← Finset.mul_sum,coordinates_sq_norm]
  have hn := mul_nonneg hM (norm_nonneg x)
  nlinarith only [hsq,hn,norm_nonneg y]

/-- Coordinate formula for an arbitrary gradient step. -/
theorem coordinates_step {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) (s : ℝ) (v : V)
    (μ : Eigenvalues H) :
    coordinates hH (v-s • H v) μ = (1-s*(μ:ℝ)) • coordinates hH v μ := by
  unfold coordinates
  rw [map_sub,map_smul]
  change hH.diagonalization v μ-s • hH.diagonalization (H v) μ = _
  rw [hH.diagonalization_apply_self_apply,smul_smul,sub_smul,one_smul]

/-- A uniform bound for arbitrary spectral gradient multipliers. -/
theorem gradient_step_norm_bound {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {s M : ℝ} (hM : 0 ≤ M) (hmult : ∀ μ : Eigenvalues H, |1-s*(μ:ℝ)| ≤ M) (v : V) :
    ‖v-s • H v‖ ≤ M*‖v‖ :=
  coordinate_multiplier_norm_bound hH (fun μ => 1-s*(μ:ℝ)) hM
    (coordinates_step hH s v) hmult

/-- The manuscript's exact one-step spectral norm bound in the original Euclidean space. -/
theorem spectral_step_norm_bound {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hslo : 1/b ≤ s) (hshi : s ≤ 1/a) (v : V) :
    ‖v-s • H v‖ ≤ (b/a-1)*‖v‖ := by
  have hd : 0 ≤ b/a-1 := by have := (one_le_div ha).mpr hab; linarith
  exact gradient_step_norm_bound hH hd
    (fun μ => BB.Spectral.multiplier_bound ha hab (hspec μ).1 (hspec μ).2 hslo hshi) v

/-- A convenient enlarged growth constant, including the value one. -/
theorem spectral_step_norm_bound_max {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {a b s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hslo : 1/b ≤ s) (hshi : s ≤ 1/a) (v : V) :
    ‖v-s • H v‖ ≤ max 1 (b/a-1)*‖v‖ :=
  (spectral_step_norm_bound hH ha hab hspec hslo hshi v).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg v))

/-- Operator norm control from the upper spectral endpoint. -/
theorem hessian_norm_bound {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {b : ℝ}
    (hb : 0 ≤ b) (hspec : ∀ μ : Eigenvalues H, |(μ:ℝ)| ≤ b) (v : V) :
    ‖H v‖ ≤ b*‖v‖ := by
  apply coordinate_multiplier_norm_bound hH (fun μ => (μ:ℝ)) hb ?_ hspec
  intro μ
  exact hH.diagonalization_apply_self_apply v μ

/-- Positive spectral endpoints give both coercivity and Hessian norm control. -/
theorem positive_spectral_bounds {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b) (v : V) :
    a*‖v‖^2 ≤ @inner ℝ _ _ v (H v) ∧ ‖H v‖ ≤ b*‖v‖ := by
  constructor
  · exact (quadratic_bounds_of_spectral_bounds hH hspec v).1
  · apply hessian_norm_bound hH (le_trans ha.le hab) ?_ v
    intro μ
    rw [abs_of_nonneg (le_trans ha.le (hspec μ).1)]
    exact (hspec μ).2

/-- The lower spectral endpoint also controls the norm of the Hessian action. -/
theorem hessian_norm_lower {H : V →ₗ[ℝ] V} {a : ℝ} (ha : 0 ≤ a)
    (hcoercive : ∀ v : V, a*‖v‖^2 ≤ @inner ℝ _ _ v (H v)) (v : V) :
    a*‖v‖ ≤ ‖H v‖ := by
  by_cases hv : v = 0
  · simp [hv]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hh := (hcoercive v).trans (real_inner_le_norm v (H v))
  have hprod : (a*‖v‖)*‖v‖ ≤ ‖H v‖*‖v‖ := by nlinarith only [hh]
  exact (mul_le_mul_right hvpos).mp hprod

end BB.Operator
