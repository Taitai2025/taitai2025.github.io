import BB.BorelPolynomial
import BB.HilbertWeightedSharpness

/-!
# Borel weights on genuine eigenspaces

The scalar measure of every eigenvector is proved to be its squared norm times
a Dirac mass. Symmetry and commutation then identify the full vector action of
the constructed Borel operator, allowing exact weighted endpoint trajectories.
-/

noncomputable section
namespace BB
open MeasureTheory Set
open scoped Topology NNReal ENNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma operator_iterate_eigenvector (A : E →L[ℝ] E) (r : ℝ) (x : E)
    (hx : A x = r • x) (k : ℕ) : (A : E → E)^[k] x = r^k • x := by
  induction k with
  | zero => simp only [Function.iterate_zero_apply, pow_zero, one_smul]
  | succ k ih => rw [Function.iterate_succ_apply', ih, _root_.map_smul, hx, smul_smul, pow_succ]

variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)

/-- A genuine eigenvector has exactly a Dirac scalar spectral measure. -/
theorem operator_spectral_measure_eigenvector (r : Icc a b) (x : E) (hx : A x = (r : ℝ) • x) :
    operatorSpectralMeasure A hA a b hbounds x =
      (⟨Real.toNNReal (‖x‖^2) • Measure.dirac r,
        inferInstance⟩ : FiniteMeasure (Icc a b)) := by
  apply finite_measure_eq_of_moments a b
  intro k
  rw [operator_spectral_measure_moment, operator_iterate_eigenvector A (r : ℝ) x hx,
    inner_smul_right, real_inner_self_eq_norm_sq]
  simp only [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def,
    smul_eq_mul, FiniteMeasure.toMeasure, integral_dirac, Real.coe_toNNReal _ (sq_nonneg _)]
  ring

theorem operator_spectral_eigenvector_integral (r : Icc a b) (x : E)
    (hx : A x = (r : ℝ) • x) (ψ : Icc a b → ℝ) :
    (∫ t, ψ t ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b))) = ‖x‖^2 * ψ r := by
  rw [operator_spectral_measure_eigenvector A hA a b hbounds r x hx]
  simp only [FiniteMeasure.toMeasure_smul, integral_smul_nnreal_measure, NNReal.smul_def,
    smul_eq_mul, FiniteMeasure.toMeasure, integral_dirac, Real.coe_toNNReal _ (sq_nonneg _)]

/-- A symmetric operator commuting with A is identified on an eigenspace by
its diagonal quadratic form there. -/
theorem commuting_operator_eigenvector_of_form (W : E →L[ℝ] E)
    (hW : W.toLinearMap.IsSymmetric) (hcomm : ∀ x, W (A x) = A (W x))
    (r c : ℝ) (hdiag : ∀ z, A z = r • z → ⟪W z, z⟫ = c * ‖z‖^2)
    (x : E) (hx : A x = r • x) : W x = c • x := by
  let y : E := W x - c • x
  have hy : A y = r • y := by
    dsimp only [y]
    rw [map_sub, _root_.map_smul, ← hcomm, hx, _root_.map_smul]
    rw [smul_sub, smul_smul, smul_smul, mul_comm c r]
  have hplus : A (x+y) = r • (x+y) := by rw [map_add, hx, hy, smul_add]
  have hminus : A (x-y) = r • (x-y) := by
    calc
      _ = A x - A y := map_sub A x y
      _ = r • x - r • y := by rw [hx, hy]
      _ = _ := (smul_sub r x y).symm
  have hcross : ⟪W x, y⟫ = c * ⟪x, y⟫ := by
    rw [symmetric_operator_polarization W hW, hdiag _ hplus, hdiag _ hminus,
      norm_add_sq_real x y, norm_sub_sq_real x y]
    ring
  have hz : ⟪y, y⟫ = 0 := by
    change ⟪W x - c • x, y⟫ = 0
    rw [inner_sub_left, inner_smul_left, conj_trivial, hcross]
    ring
  exact sub_eq_zero.mp (inner_self_eq_zero.mp hz)

section BorelEigen
variable [CompleteSpace E]
variable (ψ : Icc a b → ℝ) (hψ : Measurable ψ)
  (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u)
  (hψbounds : ∀ t, l ≤ ψ t ∧ ψ t ≤ u)

/-- The constructed Borel operator acts by Ψ(r) on every r-eigenvector. -/
theorem borel_weight_operator_eigenvector (r : Icc a b) (x : E) (hx : A x = (r : ℝ) • x) :
    borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds x = ψ r • x := by
  apply commuting_operator_eigenvector_of_form A _
    (borel_weight_operator_symmetric A hA a b hbounds ψ hψ l u hl hlu hψbounds)
    (fun z => congrArg (fun T : E →L[ℝ] E => T z)
      (borel_weight_operator_commute A hA a b hbounds ψ hψ l u hl hlu hψbounds).eq)
    (r : ℝ) (ψ r) _ x hx
  intro z hz
  rw [borel_weight_operator_self, operator_spectral_eigenvector_integral A hA a b hbounds r z hz]
  ring

/-- Exact weighted endpoint orbits for the actual Borel operator, with the
source's Ψ-weighted balance. -/
theorem borel_weighted_endpoint_matched_orbit (r s : Icc a b)
    (hr : 0 < (r : ℝ)) (hrs : (r : ℝ) < s) (p q : E)
    (hp : A p = (r : ℝ) • p) (hq : A q = (s : ℝ) • q)
    (hp0 : p ≠ 0) (hbal : ψ r * ‖p‖^2 = ψ s * ‖q‖^2) :
    let W := borelWeightOperator A hA a b hbounds ψ hψ l u hl hlu hψbounds
    let g := hilbertEndpointOrbit (r : ℝ) (s : ℝ) p q
    g 0 ≠ 0 ∧ 0 < operatorWeightedBB A.toLinearMap W.toLinearMap (g 0) ∧
      g 1 = operatorGradientStep A.toLinearMap (operatorWeightedBB A.toLinearMap W.toLinearMap (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep A.toLinearMap
        (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate (r : ℝ) (s : ℝ))^n * ‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖/‖g 0‖) = rate (r : ℝ) (s : ℝ) := by
  exact hilbert_weighted_endpoint_matched_orbit A.toLinearMap _ hA (r : ℝ) (s : ℝ)
    (ψ r) (ψ s) hr hrs (hl.trans_le (hψbounds r).1) p q hp hq
    (borel_weight_operator_eigenvector A hA a b hbounds ψ hψ l u hl hlu hψbounds r p hp)
    (borel_weight_operator_eigenvector A hA a b hbounds ψ hψ l u hl hlu hψbounds s q hq) hp0 hbal

end BorelEigen
end BB
