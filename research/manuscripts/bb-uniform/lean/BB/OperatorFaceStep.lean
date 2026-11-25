import BB.OperatorEndpointSupport
import BB.OperatorLipschitz

/-! # Endpoint contraction on every actual spectral face

The quotient range uses only the support of its argument.  No endpoint
presence is assumed: the closed bounds include singleton supports and the
endpoint product is allowed to vanish.  The zero state is handled explicitly.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Operator
open Module.End
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem weightedAlpha_bounds_on_support {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) ≤ (hi : ℝ))
    {u : E} (hs : intervalSupported hH lo hi u) (hu : u ≠ 0) :
    1/(hi : ℝ) ≤ weightedAlpha H W u ∧ weightedAlpha H W u ≤ 1/(lo : ℝ) := by
  let e : Eigenvalues H → ℝ := fun mu => blockEnergy W mu (coordinates hH u mu)
  have he : ∀ mu, 0 ≤ e mu := fun mu => blockEnergy_nonneg hW mu (coordinates hH u mu)
  have hnum : 0 < BB.Spectral.numerator (fun _ : Eigenvalues H => 1) e := by
    have h := hW u hu
    rw [mixed_inner_decomposition hH hcomm] at h
    simpa only [BB.Spectral.numerator,one_mul,e,blockEnergy] using h
  have hsupport : ∀ mu : Eigenvalues H,
      e mu=0 ∨ ((lo : ℝ) ≤ (mu : ℝ) ∧ (mu : ℝ) ≤ (hi : ℝ)) := by
    intro mu
    by_cases hout : (mu : ℝ) < (lo : ℝ) ∨ (hi : ℝ) < (mu : ℝ)
    · left
      simp [e,blockEnergy,hs mu hout]
    · push_neg at hout
      exact Or.inr hout
  have halpha : weightedAlpha H W u = BB.Spectral.alpha
      (fun mu : Eigenvalues H => (mu : ℝ)) (fun _ => 1) e := by
    rw [weightedAlpha_blocks hH hcomm]
    simp only [BB.Blocks.blockAlpha,BB.Spectral.alpha,BB.Spectral.numerator,
      BB.Spectral.denominator,one_mul,e]
  rw [halpha]
  exact BB.Spectral.alpha_bounds_on_support ha hab he (fun _ => by norm_num) hsupport hnum

def actualEndpointProduct {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) (z : E × E) : ℝ :=
  BB.geometricProduct (BB.endpointTheta (lo : ℝ) (hi : ℝ))
    ‖coordinates hH z.2 lo‖ ‖coordinates hH z.2 hi‖

theorem actualEndpointProduct_zero {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ)) :
    actualEndpointProduct hH lo hi 0=0 := by
  unfold actualEndpointProduct
  apply (BB.geometricProduct_eq_zero_iff (BB.endpointTheta_pos ha hab)
    (BB.endpointTheta_lt_one ha hab) (norm_nonneg _) (norm_nonneg _)).mpr
  left
  simp [coordinates]

theorem actualEndpointProduct_step {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    {M : ℝ} {z : E × E} (hc : stateCone M z) (hs : intervalSupported hH lo hi z.1) :
    actualEndpointProduct hH lo hi (stateMap H W z) ≤
      BB.endpointRate (lo : ℝ) (hi : ℝ)*actualEndpointProduct hH lo hi z := by
  by_cases hu : z.1=0
  · have hz := stateCone_zero_of_fst_zero hc hu
    rw [hz,stateMap_zero,actualEndpointProduct_zero hH ha hab,mul_zero]
  · obtain ⟨hlo,hhi⟩ := weightedAlpha_bounds_on_support hH hcomm hW ha hab.le hs hu
    unfold actualEndpointProduct
    change BB.geometricProduct _
      ‖coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) lo‖
      ‖coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) hi‖ ≤ _
    rw [coordinates_step,coordinates_step,norm_smul,norm_smul,
      Real.norm_eq_abs,Real.norm_eq_abs]
    exact BB.endpointProduct_decay_stepsize ha hab hlo hhi (norm_nonneg _) (norm_nonneg _)

end BB.Operator
