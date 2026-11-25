import BB.PropertyBComparison
import BB.SortedOperator
import BB.OperatorCondition
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Analytic.Constructions

/-! # The actual operator comparison with a fixed positive analytic spectral weight

The operator Ψ(H) is defined by the proved orthogonal eigenspace decomposition.
No simultaneous diagonalization of the varying commuting weight W is assumed.
Its effective scalar weights are derived from its quadratic forms on H's blocks.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Operator

open Module.End InnerProductSpace
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Finite-dimensional spectral functional calculus, on the actual eigenspaces. -/
def spectralFunction {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (psi : ℝ → ℝ) : E →ₗ[ℝ] E where
  toFun u := hH.diagonalization.symm
    (fun mu : Eigenvalues H => psi (mu:ℝ) • hH.diagonalization u mu)
  map_add' u v := by
    apply hH.diagonalization.injective
    simp only [map_add,LinearIsometryEquiv.apply_symm_apply]
    ext mu
    simp only [PiLp.add_apply,smul_add]
  map_smul' t u := by
    apply hH.diagonalization.injective
    simp only [map_smul,LinearIsometryEquiv.apply_symm_apply]
    ext mu
    simp only [PiLp.smul_apply,smul_smul,RingHom.id_apply,mul_comm]

theorem spectralFunction_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (psi : ℝ → ℝ) (u : E) (mu : Eigenvalues H) :
    hH.diagonalization (spectralFunction hH psi u) mu =
      psi (mu:ℝ) • hH.diagonalization u mu :=
  congrArg (fun y => y mu) (hH.diagonalization.apply_symm_apply _)

theorem spectralFunction_commutes {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (psi : ℝ → ℝ) : Function.Commute H (spectralFunction hH psi) := by
  intro u
  apply hH.diagonalization.injective
  ext mu
  rw [hH.diagonalization_apply_self_apply,spectralFunction_coordinates,
    spectralFunction_coordinates,hH.diagonalization_apply_self_apply]
  rw [smul_smul,smul_smul,mul_comm]

/-- The spectral isometry gives the exact bilinear form of Ψ(H). -/
theorem spectralFunction_inner {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (psi : ℝ → ℝ) (u v : E) :
    ⟪u,spectralFunction hH psi v⟫_ℝ =
      ∑ mu : Eigenvalues H, psi (mu:ℝ)*⟪hH.diagonalization u mu,hH.diagonalization v mu⟫_ℝ := by
  rw [← hH.diagonalization.inner_map_map,PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro mu _
  rw [spectralFunction_coordinates,real_inner_smul_right]

theorem spectralFunction_symmetric {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (psi : ℝ → ℝ) : (spectralFunction hH psi).IsSymmetric := by
  intro u v
  have hc : ⟪spectralFunction hH psi u,v⟫_ℝ =
      ⟪v,spectralFunction hH psi u⟫_ℝ := real_inner_comm _ _
  rw [hc,spectralFunction_inner,spectralFunction_inner]
  apply Finset.sum_congr rfl
  intro mu _
  rw [real_inner_comm]

theorem spectralFunction_quadratic {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (psi : ℝ → ℝ) (u : E) :
    ⟪u,spectralFunction hH psi u⟫_ℝ =
      ∑ mu : Eigenvalues H, psi (mu:ℝ)*‖coordinates hH u mu‖^2 := by
  rw [spectralFunction_inner]
  simp only [real_inner_self_eq_norm_sq,coordinates]

theorem spectralFunction_positive {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {psi : ℝ → ℝ} (hpsi : ∀ mu : Eigenvalues H, 0 < psi (mu:ℝ))
    {u : E} (hu : u ≠ 0) : 0 < ⟪u,spectralFunction hH psi u⟫_ℝ := by
  have hex : ∃ mu : Eigenvalues H, coordinates hH u mu ≠ 0 := by
    by_contra! hzero
    apply hu
    apply hH.diagonalization.injective
    ext1 mu
    simpa only [coordinates,map_zero,PiLp.zero_apply] using hzero mu
  obtain ⟨mu,hmu⟩ := hex
  rw [spectralFunction_quadratic]
  exact Finset.sum_pos'
    (fun nu _ => mul_nonneg (hpsi nu).le (sq_nonneg _))
    ⟨mu,Finset.mem_univ _,mul_pos (hpsi mu) (sq_pos_of_pos (norm_pos_iff.mpr hmu))⟩

theorem spectralFunction_moment {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (psi : ℝ → ℝ) (u : E) :
    ⟪u,spectralFunction hH psi (H u)⟫_ℝ =
      ∑ mu : Eigenvalues H, psi (mu:ℝ)*(mu:ℝ)*‖coordinates hH u mu‖^2 := by
  rw [spectralFunction_inner]
  apply Finset.sum_congr rfl
  intro mu _
  rw [hH.diagonalization_apply_self_apply,real_inner_smul_right,
    real_inner_self_eq_norm_sq]
  dsimp only [coordinates]
  ring

/-- Exact quotient for Ψ(H), reindexed by the increasing distinct spectrum. -/
theorem weightedAlpha_spectralFunction_sorted {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {n : ℕ} (hn : Fintype.card (Eigenvalues H)=n) (psi : ℝ → ℝ) (u : E) :
    weightedAlpha H (spectralFunction hH psi) u =
      BB.Spectral.alpha (sortedLambda H hn) (fun i => psi (sortedLambda H hn i))
        (fun i => ‖sortedCoordinates hH hn u i‖^2) := by
  unfold weightedAlpha BB.Spectral.alpha BB.Spectral.numerator BB.Spectral.denominator
  rw [spectralFunction_quadratic,spectralFunction_moment]
  congr 1
  · exact ((spectralIndex H hn).toEquiv.sum_comp
      (fun mu => psi (mu:ℝ)*‖coordinates hH u mu‖^2)).symm
  · exact ((spectralIndex H hn).toEquiv.sum_comp
      (fun mu => psi (mu:ℝ)*(mu:ℝ)*‖coordinates hH u mu‖^2)).symm

/-- The scalar function used in the introduction is strictly positive everywhere. -/
theorem exponentialWeight_positive (t x : ℝ) : 0 < Real.exp (-t*x) := Real.exp_pos _

/-- The same scalar function is real analytic on the whole real line. -/
theorem exponentialWeight_analytic (t x : ℝ) :
    AnalyticAt ℝ (fun y : ℝ => Real.exp (-t*y)) x := by
  rw [Real.exp_eq_exp_ℝ]
  exact (NormedSpace.exp_analytic (-t*x)).comp (analyticAt_const.mul (analyticAt_id ℝ x))

/-- The fixed operator exp(-tH), defined by its spectral functional calculus. -/
def exponentialWeightOperator {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (t : ℝ) : E →ₗ[ℝ] E :=
  spectralFunction hH (fun x => Real.exp (-t*x))

theorem exponentialWeightOperator_symmetric {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (t : ℝ) :
    (exponentialWeightOperator hH t).IsSymmetric := spectralFunction_symmetric hH _

theorem exponentialWeightOperator_commutes {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (t : ℝ) :
    Function.Commute H (exponentialWeightOperator hH t) := spectralFunction_commutes hH _

theorem exponentialWeightOperator_positive {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (t : ℝ)
    {u : E} (hu : u ≠ 0) : 0 < ⟪u,exponentialWeightOperator hH t u⟫_ℝ :=
  spectralFunction_positive hH (psi := fun x => Real.exp (-t*x))
    (fun _ => Real.exp_pos _) hu

/-- For an arbitrary commuting W, normalized block energies supply all effective
scalar weights in [1,chi], including the zero-block convention. -/
theorem weightedAlpha_effective_sorted {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) {n : ℕ} (hn : Fintype.card (Eigenvalues H)=n)
    {m chi : ℝ} (hm : 0 < m)
    (hq : ∀ x : E, m*‖x‖^2 ≤ ⟪x,W x⟫_ℝ ∧ ⟪x,W x⟫_ℝ ≤ (chi*m)*‖x‖^2)
    (u : E) :
    weightedAlpha H W u = BB.Spectral.alpha (sortedLambda H hn)
      (BB.Blocks.effectiveWeight (fun i x => sortedEnergy hn W i x/m)
        (sortedCoordinates hH hn u))
      (fun i => ‖sortedCoordinates hH hn u i‖^2) := by
  have hb := sortedEnergy_bounds hn (fun x => (hq x).1) (fun x => (hq x).2)
  have hnq := BB.Blocks.normalized_energy_bounds hm hb.1 hb.2
  rw [weightedAlpha_sorted hH hcomm hn,
    ← BB.Blocks.blockAlpha_scale (sortedLambda H hn) (sortedEnergy hn W)
      (sortedCoordinates hH hn u) hm.ne',
    BB.Blocks.blockAlpha_eq hnq.1 hnq.2,BB.Spectral.vectorAlpha_eq]
  rfl

/-- The literal operator quotient comparison from the introduction, with energy
bounds equivalent to the condition-number constraint. The fixed comparison
operator depends only on H and t, not on W or the nonzero vector u. -/
theorem exponential_operator_comparison_of_energy {H W : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (hHpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ)
    (hcomm : Function.Commute H W) {n : ℕ} (hn : Fintype.card (Eigenvalues H)=n+2)
    {m chi Delta t : ℝ} (hm : 0 < m) (hchi : 1 ≤ chi) (hDelta : 0 < Delta)
    (hq : ∀ x : E, m*‖x‖^2 ≤ ⟪x,W x⟫_ℝ ∧ ⟪x,W x⟫_ℝ ≤ (chi*m)*‖x‖^2)
    (hgap : ∀ i : Fin (n+1), Delta ≤ sortedLambda H hn i.succ-sortedLambda H hn i.castSucc)
    (ht : t*Delta ≥ Real.log chi) {u : E} (hu : u ≠ 0) :
    weightedAlpha H W u ≤ weightedAlpha H (exponentialWeightOperator hH t) u := by
  have hb := sortedEnergy_bounds hn (fun x => (hq x).1) (fun x => (hq x).2)
  have hnq := BB.Blocks.normalized_energy_bounds hm hb.1 hb.2
  have hw := BB.Blocks.effectiveWeight_bounds hchi hnq.1 hnq.2 (sortedCoordinates hH hn u)
  have hmass : 0 < BB.Spectral.mass (fun i => ‖sortedCoordinates hH hn u i‖^2) := by
    unfold BB.Spectral.mass
    rw [sortedCoordinates_sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hu)
  rw [weightedAlpha_effective_sorted hH hcomm hn hm hq]
  change _ ≤ weightedAlpha H (spectralFunction hH (fun x => Real.exp (-t*x))) u
  rw [weightedAlpha_spectralFunction_sorted hH hn]
  exact BB.Comparison.exponential_weight_comparison (sortedLambda H hn)
    (sortedLambda_strictMono H hn) (sortedLambda_pos hn hHpd 0) hchi hDelta hgap ht
    _ _ (fun i => (hw i).1) (fun i => (hw i).2) (fun _ => sq_nonneg _) hmass

/-- Condition-number form for every symmetric positive definite commuting W. -/
theorem exponential_operator_comparison {H W : E →ₗ[ℝ] E}
    [Nonempty (Eigenvalues W)]
    (hH : H.IsSymmetric) (hHpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,H x⟫_ℝ)
    (hW : W.IsSymmetric) (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W) {n : ℕ} (hn : Fintype.card (Eigenvalues H)=n+2)
    {chi Delta t : ℝ} (hchi : 1 ≤ chi) (hDelta : 0 < Delta)
    (hcond : spectralConditionNumber W ≤ chi)
    (hgap : ∀ i : Fin (n+1), Delta ≤ sortedLambda H hn i.succ-sortedLambda H hn i.castSucc)
    (ht : t*Delta ≥ Real.log chi) {u : E} (hu : u ≠ 0) :
    weightedAlpha H W u ≤ weightedAlpha H (exponentialWeightOperator hH t) u := by
  obtain ⟨m,hm,hq⟩ := energy_bounds_of_condition hW hWpd hcond
  exact exponential_operator_comparison_of_energy hH hHpd hcomm hn hm hchi hDelta hq hgap ht hu

end BB.Operator
