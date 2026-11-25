import BB.FunctionalEmbedding
import BB.FiniteCompression
import Mathlib.Topology.ContinuousFunction.Weierstrass

/-!
# Normalized operator moment states

Every finite collection of moments is realized by an exact finite Krylov
compression. Compactness of positive normalized functionals then realizes all
moments simultaneously. Polynomial density proves uniqueness.
-/

namespace BB
noncomputable section
open Set
open scoped BigOperators Topology Polynomial
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Finite
variable [FiniteDimensional ℝ E]

lemma eigen_coordinates_iterate {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (x : E) (k : ℕ) (i : Fin (FiniteDimensional.finrank ℝ E)) :
    eigenCoordinates hH ((H : E → E)^[k] x) i =
      (eigenValues hH i)^k * eigenCoordinates hH x i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', eigen_coordinates_apply, ih, pow_succ]
    ring

lemma eigen_coordinates_inner_pair {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (x y : E) :
    ⟪x,y⟫ = ∑ i, eigenCoordinates hH x i * eigenCoordinates hH y i := by
  rw [← (hH.eigenvectorBasis rfl).repr.inner_map_map x y, PiLp.inner_apply]
  rfl

lemma eigen_power_moment {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (x : E) (k : ℕ) :
    ⟪x,(H : E → E)^[k] x⟫ = ∑ i, (eigenValues hH i)^k * (eigenCoordinates hH x i)^2 := by
  rw [eigen_coordinates_inner_pair hH]
  apply Finset.sum_congr rfl
  intro i _
  rw [eigen_coordinates_iterate]
  ring

def finiteMomentState {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫ ∧ ⟪x,H x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) : PositiveState (Icc a b) :=
  simplexFunctional (fun i => ⟨eigenValues hH i, eigenvalue_bounds hH a b hbounds i⟩)
    ⟨energyWeights (eigenCoordinates hH x), energy_weights_simplex (by
      rw [eigen_coordinates_energy]
      exact sq_pos_of_pos (norm_pos_iff.mpr hx))⟩

lemma finite_moment_state_power {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,H x⟫ ∧ ⟪x,H x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (k : ℕ) :
    (finiteMomentState hH a b hbounds x hx).1 ((intervalCoordinate a b)^k) =
      ⟪x,(H : E → E)^[k] x⟫ / ‖x‖^2 := by
  rw [finiteMomentState, simplex_functional_apply, eigen_power_moment hH]
  simp only [energyWeights, ContinuousMap.pow_apply, intervalCoordinate,
    ContinuousMap.coe_mk, eigen_coordinates_energy]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

end Finite

def krylovSpace (A : E →L[ℝ] E) (x : E) (N : ℕ) : Submodule ℝ E :=
  trajectorySpace A (fun j => (A : E → E)^[j] x) N

instance krylovSpace_finite (A : E →L[ℝ] E) (x : E) (N : ℕ) :
    FiniteDimensional ℝ (krylovSpace A x N) := trajectorySpace_finite A _ N

def krylovStart (A : E →L[ℝ] E) (x : E) (N : ℕ) : krylovSpace A x N :=
  ⟨x, gradient_mem_trajectorySpace A (fun j => (A : E → E)^[j] x) N 0 (by omega)⟩

lemma krylov_iterate_matches (A : E →L[ℝ] E) (x : E) (N k : ℕ) (hk : k ≤ N) :
    (((operatorCompression A (krylovSpace A x N) : krylovSpace A x N → krylovSpace A x N)^[k]
      (krylovStart A x N) : krylovSpace A x N) : E) = (A : E → E)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    change (orthogonalProjection (krylovSpace A x N)
      (A (((operatorCompression A (krylovSpace A x N) :
        krylovSpace A x N → krylovSpace A x N)^[k] (krylovStart A x N)) : E)) : E) = _
    rw [ih (by omega)]
    exact orthogonalProjection_eq_self_iff.mpr
      (image_mem_trajectorySpace A (fun j => (A : E → E)^[j] x) N k (by omega))

lemma operator_finite_moments_exist (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (N : ℕ) :
    ∃ L : PositiveState (Icc a b), ∀ k ≤ N,
      L.1 ((intervalCoordinate a b)^k) = ⟪x,(A : E → E)^[k] x⟫/‖x‖^2 := by
  let V := krylovSpace A x N
  let y := krylovStart A x N
  have hy : y ≠ 0 := fun hz => hx (congrArg Subtype.val hz)
  let hB := compression_symmetric A hA V
  let L := finiteMomentState hB a b (compression_bounds A V a b hbounds) y hy
  refine ⟨L,?_⟩
  intro k hk
  rw [finite_moment_state_power]
  change ⟪x, (((operatorCompression A V : V → V)^[k] y : V) : E)⟫/‖x‖^2 = _
  rw [krylov_iterate_matches A x N k hk]

def momentMatchingSet (A : E →L[ℝ] E) (a b : ℝ) (x : E) (N : ℕ) :
    Set (PositiveState (Icc a b)) :=
  {L | ∀ k ≤ N, L.1 ((intervalCoordinate a b)^k) = ⟪x,(A : E → E)^[k] x⟫/‖x‖^2}

lemma moment_matching_isClosed (A : E →L[ℝ] E) (a b : ℝ) (x : E) (N : ℕ) :
    IsClosed (momentMatchingSet A a b x N) := by
  unfold momentMatchingSet
  simp only [setOf_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro _
  exact isClosed_eq (positive_state_eval_continuous _) continuous_const

theorem operator_moment_state_exists (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) :
    ∃ L : PositiveState (Icc a b), ∀ k : ℕ,
      L.1 ((intervalCoordinate a b)^k) = ⟪x,(A : E → E)^[k] x⟫/‖x‖^2 := by
  have hn : ∀ N, (momentMatchingSet A a b x N).Nonempty :=
    operator_finite_moments_exist A hA a b hbounds x hx
  have hc := moment_matching_isClosed A a b x
  obtain ⟨L,hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (momentMatchingSet A a b x) (fun N L h k hk => h k (by omega)) hn (hc 0).isCompact hc
  exact ⟨L,fun k => (mem_iInter.mp hL k) k le_rfl⟩

lemma continuous_polynomial_monomial (a b c : ℝ) (k : ℕ) :
    (Polynomial.monomial k c).toContinuousMapOn (Icc a b) = c • (intervalCoordinate a b)^k := by
  ext t
  simp [intervalCoordinate, Polynomial.toContinuousMapOn, Polynomial.toContinuousMap]

theorem positive_state_eq_of_moments (a b : ℝ) (L M : PositiveState (Icc a b))
    (h : ∀ k : ℕ, L.1 ((intervalCoordinate a b)^k) = M.1 ((intervalCoordinate a b)^k)) : L = M := by
  have hpoly : ∀ p : ℝ[X], L.1 (p.toContinuousMapOn (Icc a b)) =
      M.1 (p.toContinuousMapOn (Icc a b)) := by
    intro p
    induction p using Polynomial.induction_on' with
    | h_add p q hp hq =>
      have he : (p+q).toContinuousMapOn (Icc a b) =
          p.toContinuousMapOn (Icc a b) + q.toContinuousMapOn (Icc a b) := by
        ext t
        simp
      rw [he, map_add, map_add, hp, hq]
    | h_monomial k c =>
      rw [continuous_polynomial_monomial, map_smul, map_smul, h k]
  have hd : Dense (polynomialFunctions (Icc a b) : Set C(Icc a b,ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, polynomialFunctions_closure_eq_top]
    rfl
  have heq : (polynomialFunctions (Icc a b) : Set C(Icc a b,ℝ)) ⊆
      {f | L.1 f = M.1 f} := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨p,rfl⟩ := hf
    exact hpoly p
  have hcl : closure (polynomialFunctions (Icc a b) : Set C(Icc a b,ℝ)) ⊆
      {f | L.1 f = M.1 f} := closure_minimal heq
    (isClosed_eq (WeakDual.toNormedDual L.1).continuous (WeakDual.toNormedDual M.1).continuous)
  apply Subtype.ext
  apply DFunLike.ext
  intro f
  exact hcl (hd f)

def operatorMomentState (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) : PositiveState (Icc a b) :=
  (operator_moment_state_exists A hA a b hbounds x hx).choose

lemma operator_moment_state_power (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (k : ℕ) :
    (operatorMomentState A hA a b hbounds x hx).1 ((intervalCoordinate a b)^k) =
      ⟪x,(A : E → E)^[k] x⟫/‖x‖^2 :=
  (operator_moment_state_exists A hA a b hbounds x hx).choose_spec k

lemma operator_iterate_step (A : E →L[ℝ] E) (x : E) (α : ℝ) (k : ℕ) :
    (A : E → E)^[k] (operatorGradientStep A.toLinearMap α x) =
      (A : E → E)^[k] x - α • (A : E → E)^[k+1] x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [Function.iterate_succ_apply', ih, map_sub, map_smul]

lemma operator_moment_shift_left (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (x : E) (k : ℕ) :
    ⟪A x,(A : E → E)^[k] x⟫ = ⟪x,(A : E → E)^[k+1] x⟫ := by
  rw [Function.iterate_succ_apply']
  exact hA x ((A : E → E)^[k] x)

lemma operator_step_power_moment (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (x : E) (α : ℝ) (k : ℕ) :
    ⟪operatorGradientStep A.toLinearMap α x,
      (A : E → E)^[k] (operatorGradientStep A.toLinearMap α x)⟫ =
      ⟪x,(A : E → E)^[k] x⟫ - 2*α*⟪x,(A : E → E)^[k+1] x⟫ +
        α^2*⟪x,(A : E → E)^[k+2] x⟫ := by
  rw [operator_iterate_step]
  change ⟪x - α • A x, (A : E → E)^[k] x - α • (A : E → E)^[k+1] x⟫ = _
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    conj_trivial, smul_eq_mul]
  rw [operator_moment_shift_left A hA x k, operator_moment_shift_left A hA x (k+1)]
  ring

lemma coordinate_step_polynomial (a b α : ℝ) (k : ℕ) :
    (1-α • intervalCoordinate a b)^2 * (intervalCoordinate a b)^k =
      (intervalCoordinate a b)^k - (2*α) • (intervalCoordinate a b)^(k+1) +
        (α^2) • (intervalCoordinate a b)^(k+2) := by
  ext t
  simp only [ContinuousMap.mul_apply, ContinuousMap.pow_apply, ContinuousMap.sub_apply,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.one_apply, smul_eq_mul,
    pow_add, pow_one, pow_two]
  ring

lemma operator_step_moment_test (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (k : ℕ) :
    (operatorMomentState A hA a b hbounds x hx).1
      ((1-α • intervalCoordinate a b)^2 * (intervalCoordinate a b)^k) =
      ⟪operatorGradientStep A.toLinearMap α x,
        (A : E → E)^[k] (operatorGradientStep A.toLinearMap α x)⟫/‖x‖^2 := by
  rw [coordinate_step_polynomial, map_add, map_sub, map_smul, map_smul]
  simp only [smul_eq_mul, operator_moment_state_power]
  rw [operator_step_power_moment A hA]
  ring

lemma operator_step_density_mass (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) :
    (operatorMomentState A hA a b hbounds x hx).1 ((1-α • intervalCoordinate a b)^2) =
      ‖operatorGradientStep A.toLinearMap α x‖^2/‖x‖^2 := by
  simpa only [pow_zero, mul_one, Function.iterate_zero_apply, real_inner_self_eq_norm_sq]
    using operator_step_moment_test A hA a b hbounds x hx α 0

lemma operator_step_density_pos (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    0 < (operatorMomentState A hA a b hbounds x hx).1 ((1-α • intervalCoordinate a b)^2) := by
  rw [operator_step_density_mass]
  exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)) (sq_pos_of_pos (norm_pos_iff.mpr hx))

/-- The normalized state of the actual updated vector is exactly the positive
functional reweighted by its squared affine spectral multiplier. -/
theorem operator_moment_state_reweight (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    operatorMomentState A hA a b hbounds (operatorGradientStep A.toLinearMap α x) hy =
      positiveReweight (operatorMomentState A hA a b hbounds x hx)
        ((1-α • intervalCoordinate a b)^2)
        (by intro t; simp only [ContinuousMap.pow_apply]; exact sq_nonneg _)
        (operator_step_density_pos A hA a b hbounds x hx α hy) := by
  apply positive_state_eq_of_moments
  intro k
  rw [operator_moment_state_power, positiveReweight_apply, operator_step_moment_test,
    operator_step_density_mass]
  have hn : ‖x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
  field_simp

lemma operator_moment_state_mean (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) :
    (operatorMomentState A hA a b hbounds x hx).1 (intervalCoordinate a b) =
      ⟪x,A x⟫/‖x‖^2 := by
  simpa only [pow_one, Function.iterate_one] using operator_moment_state_power A hA a b hbounds x hx 1

lemma operator_bb1_moment_mean (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x : E) (hx : x ≠ 0) :
    operatorBB1 A.toLinearMap x =
      ((operatorMomentState A hA a b hbounds x hx).1 (intervalCoordinate a b))⁻¹ := by
  rw [operator_moment_state_mean, inv_div]
  rfl

def operatorMomentPair (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) : FunctionalState (Icc a b) :=
  (operatorMomentState A hA a b hbounds x hx, operatorMomentState A hA a b hbounds z hz)

lemma operator_moment_pair_multiplier (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) :
    quadraticMultiplier (intervalCoordinate a b)
      (functionalMean (intervalCoordinate a b) (operatorMomentPair A hA a b hbounds x z hx hz)) =
      (1-operatorBB1 A.toLinearMap z • intervalCoordinate a b)^2 := by
  change (1-((operatorMomentState A hA a b hbounds z hz).1 (intervalCoordinate a b))⁻¹ •
    intervalCoordinate a b)^2 = _
  rw [← operator_bb1_moment_mean]

lemma operator_moment_pair_growth_sq (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) :
    functionalGrowthSq (intervalCoordinate a b) (operatorMomentPair A hA a b hbounds x z hx hz) =
      ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x‖^2 / ‖x‖^2 := by
  unfold functionalGrowthSq
  rw [operator_moment_pair_multiplier]
  exact operator_step_density_mass A hA a b hbounds x hx _

lemma operator_moment_pair_norm_ratio (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0) :
    ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x‖ / ‖x‖ =
      functionalGrowth (intervalCoordinate a b) (operatorMomentPair A hA a b hbounds x z hx hz) := by
  rw [functionalGrowth, operator_moment_pair_growth_sq, Real.sqrt_div (sq_nonneg _),
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- The normalized functional pair of actual vectors obeys the exact BB map. -/
theorem operator_moment_pair_update (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (x z : E) (hx : x ≠ 0) (hz : z ≠ 0)
    (hy : operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x ≠ 0) :
    operatorMomentPair A hA a b hbounds
      (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x) x hy hx =
      functionalMap (intervalCoordinate a b) (operatorMomentPair A hA a b hbounds x z hx hz) := by
  have hR : 0 < functionalGrowthSq (intervalCoordinate a b)
      (operatorMomentPair A hA a b hbounds x z hx hz) := by
    rw [operator_moment_pair_growth_sq]
    exact div_pos (sq_pos_of_pos (norm_pos_iff.mpr hy)) (sq_pos_of_pos (norm_pos_iff.mpr hx))
  apply Prod.ext
  · apply positive_state_eq_of_moments
    intro k
    change (operatorMomentState A hA a b hbounds
      (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x) hy).1
      ((intervalCoordinate a b)^k) = _
    rw [operator_moment_state_power, functional_map_regular_test _ _ _ hR,
      operator_moment_pair_multiplier, operator_moment_pair_growth_sq]
    change _ = (operatorMomentState A hA a b hbounds x hx).1
      ((1-operatorBB1 A.toLinearMap z • intervalCoordinate a b)^2 *
        (intervalCoordinate a b)^k) / _
    rw [operator_step_moment_test]
    have hn : ‖x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
    field_simp
  · exact (functional_map_regular _ _ hR).2.symm

end
end BB
