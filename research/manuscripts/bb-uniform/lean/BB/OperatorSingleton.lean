import BB.MainTheorem

set_option autoImplicit false

noncomputable section
namespace BB.Operator
open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual weighted quotient of a nonzero eigenvector is the reciprocal
eigenvalue, for every positive weight. -/
theorem weightedAlpha_eigenvector {H W : E →ₗ[ℝ] E} {a : ℝ} (ha : 0 < a)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x)) {u : E}
    (hu : H u = a • u) (hu0 : u ≠ 0) : weightedAlpha H W u = 1/a := by
  have hE := hW u hu0
  unfold weightedAlpha
  rw [hu,W.map_smul,inner_smul_right]
  field_simp
  ring

/-- A state supported in one actual eigenspace loses its current gradient in
one update. Cone admissibility handles the zero-predecessor case. -/
theorem stateMap_single_eigenvalue {H W : E →ₗ[ℝ] E} {a M : ℝ} (ha : 0 < a)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x)) {z : E × E}
    (hz : stateCone M z) (hu : H z.1 = a • z.1) (hv : H z.2 = a • z.2) :
    stateMap H W z = (z.2,0) := by
  by_cases hu0 : z.1 = 0
  · have hv0 : z.2 = 0 := by
      apply norm_eq_zero.mp
      apply le_antisymm _ (norm_nonneg _)
      simpa only [stateCone,hu0,norm_zero,mul_zero] using hz
    simp only [stateMap,hu0,hv0,map_zero,smul_zero,sub_zero]
  · unfold stateMap
    rw [weightedAlpha_eigenvector ha hW hu hu0,hv,smul_smul,one_div_mul_cancel ha.ne',one_smul,sub_self]

/-- Two actual state updates terminate a one-eigenvalue tail, with an arbitrary
weight allowed on the final update. -/
theorem two_updates_single_eigenvalue {H W W' : E →ₗ[ℝ] E} {a M : ℝ} (ha : 0 < a)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x)) {z : E × E}
    (hz : stateCone M z) (hu : H z.1 = a • z.1) (hv : H z.2 = a • z.2) :
    stateMap H W' (stateMap H W z) = 0 := by
  rw [stateMap_single_eigenvalue ha hW hz hu hv]
  simp only [stateMap,map_zero,smul_zero,sub_zero]
  rfl

variable [FiniteDimensional ℝ E]

/-- A symmetric operator with a singleton spectrum is the corresponding scalar
operator, proved from the actual spectral isometry. -/
theorem scalar_operator_of_singleton_spectrum {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a : ℝ} (hspec : ∀ mu : Eigenvalues H, (mu:ℝ) = a) (u : E) : H u = a • u := by
  apply hH.diagonalization.injective
  rw [map_smul]
  apply PiLp.ext
  intro mu
  change hH.diagonalization (H u) mu = a • hH.diagonalization u mu
  rw [hH.diagonalization_apply_self_apply]
  exact congrArg (fun s : ℝ => s • hH.diagonalization u mu) (hspec mu)

/-- The actual-operator singleton-spectrum termination corollary. -/
theorem singleton_spectrum_termination {H W W' : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a M : ℝ} (ha : 0 < a) (hspec : ∀ mu : Eigenvalues H, (mu:ℝ) = a)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x)) {z : E × E}
    (hz : stateCone M z) : stateMap H W' (stateMap H W z) = 0 :=
  two_updates_single_eigenvalue ha hW hz
    (scalar_operator_of_singleton_spectrum hH hspec z.1)
    (scalar_operator_of_singleton_spectrum hH hspec z.2)

end BB.Operator
