import BB.BorelMomentExtension
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Genuine Borel weighted quadratic and bilinear forms

The input measures are required only to have the actual operator moments. Their
quadratic and bilinear dependence on the vector is proved by extending finite
moment identities to the Borel test, using `integral_relation_of_moments`.
-/

noncomputable section
namespace BB
open MeasureTheory Set
open scoped Topology BigOperators
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma operator_iterate_add (A : E →L[ℝ] E) (x y : E) (k : ℕ) :
    (A : E → E)^[k] (x + y) = (A : E → E)^[k] x + (A : E → E)^[k] y := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, map_add]

lemma operator_iterate_smul (A : E →L[ℝ] E) (x : E) (c : ℝ) (k : ℕ) :
    (A : E → E)^[k] (c • x) = c • (A : E → E)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, _root_.map_smul]

variable {a b : ℝ}

/-- The scalar integral is defined before any quadratic identity is known. -/
def momentQuadraticValue (μ : E → FiniteMeasure (Icc a b)) (ψ : Icc a b → ℝ) (x : E) : ℝ :=
  ∫ t, ψ t ∂(μ x : Measure (Icc a b))

variable (A : E →L[ℝ] E) (μ : E → FiniteMeasure (Icc a b))
    (hμ : ∀ (x : E) (k : ℕ), (∫ t, (t : ℝ)^k ∂(μ x : Measure (Icc a b))) =
      ⟪x, (A : E → E)^[k] x⟫)
    (ψ : Icc a b → ℝ) (hψ : ∀ x, Integrable ψ (μ x : Measure (Icc a b)))


theorem momentQuadratic_smul (c : ℝ) (x : E) :
    momentQuadraticValue μ ψ (c • x) = c * c * momentQuadraticValue μ ψ x := by
  have h := integral_relation_of_moments a b
    (fun i : Fin 2 => μ (![c • x, x] i)) (![1, -(c*c)])
    (by
      intro k
      norm_num [Fin.sum_univ_succ, hμ, operator_iterate_smul,
        inner_smul_left, inner_smul_right]
      ring)
    ψ (fun i => hψ _)
  norm_num [Fin.sum_univ_succ] at h
  unfold momentQuadraticValue
  linarith only [h]

theorem momentQuadratic_polar_add (x y z : E) :
    QuadraticForm.polar (momentQuadraticValue μ ψ) (x + y) z =
      QuadraticForm.polar (momentQuadraticValue μ ψ) x z +
      QuadraticForm.polar (momentQuadraticValue μ ψ) y z := by
  have h := integral_relation_of_moments a b
    (fun i : Fin 7 => μ (![x+y+z, x, y, z, x+y, x+z, y+z] i))
    (![1, 1, 1, 1, -1, -1, -1])
    (by
      intro k
      norm_num [Fin.sum_univ_succ, hμ, operator_iterate_add,
        inner_add_left, inner_add_right]
      ring)
    ψ (fun i => hψ _)
  norm_num [Fin.sum_univ_succ] at h
  dsimp only [QuadraticForm.polar, momentQuadraticValue]
  linarith only [h]

theorem momentQuadratic_polar_smul (c : ℝ) (x y : E) :
    QuadraticForm.polar (momentQuadraticValue μ ψ) (c • x) y =
      c • QuadraticForm.polar (momentQuadraticValue μ ψ) x y := by
  have h := integral_relation_of_moments a b
    (fun i : Fin 6 => μ (![c • x+y, c • x, y, x+y, x, y] i))
    (![1, -1, -1, -c, c, c])
    (by
      intro k
      norm_num [Fin.sum_univ_succ, hμ, operator_iterate_add, operator_iterate_smul,
        inner_add_left, inner_add_right, inner_smul_left, inner_smul_right]
      ring)
    ψ (fun i => hψ _)
  norm_num [Fin.sum_univ_succ] at h
  dsimp only [QuadraticForm.polar, momentQuadraticValue, smul_eq_mul]
  nlinarith only [h]

/-- The actual Borel integrals have now been proved to form a quadratic form. -/
def momentQuadratic : QuadraticForm ℝ E :=
  QuadraticForm.ofPolar (momentQuadraticValue μ ψ)
    (momentQuadratic_smul A μ hμ ψ hψ)
    (momentQuadratic_polar_add A μ hμ ψ hψ)
    (momentQuadratic_polar_smul A μ hμ ψ hψ)

@[simp] theorem momentQuadratic_apply (x : E) :
    momentQuadratic A μ hμ ψ hψ x = momentQuadraticValue μ ψ x := rfl

/-- Polarization of the proved quadratic form. -/
def momentBilinear : LinearMap.BilinForm ℝ E := QuadraticForm.associated (momentQuadratic A μ hμ ψ hψ)

@[simp] theorem momentBilinear_self (x : E) :
    momentBilinear A μ hμ ψ hψ x x = momentQuadraticValue μ ψ x :=
  QuadraticForm.associated_eq_self_apply ℝ (momentQuadratic A μ hμ ψ hψ) x

theorem momentBilinear_symmetric : (momentBilinear A μ hμ ψ hψ).IsSymm :=
  QuadraticForm.associated_isSymm ℝ (momentQuadratic A μ hμ ψ hψ)

theorem momentBilinear_apply (x y : E) :
    momentBilinear A μ hμ ψ hψ x y =
      (momentQuadraticValue μ ψ (x+y) - momentQuadraticValue μ ψ x - momentQuadraticValue μ ψ y) / 2 := by
  rw [momentBilinear, QuadraticForm.associated_apply]
  simp only [momentQuadratic_apply, invOf_eq_inv]
  ring

/-- The zero moment gives the exact total mass, including x=0. -/
theorem momentMeasure_mass (x : E) : ((μ x : Measure (Icc a b)) univ).toReal = ‖x‖^2 := by
  have h := hμ x 0
  simpa only [pow_zero, integral_const, smul_eq_mul, mul_one,
    Function.iterate_zero, id_eq, real_inner_self_eq_norm_sq] using h

/-- The Borel weight bounds give exactly the requested norm-equivalence constants. -/
theorem momentQuadratic_bounds (l u : ℝ) (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) (x : E) :
    l * ‖x‖^2 ≤ momentQuadraticValue μ ψ x ∧ momentQuadraticValue μ ψ x ≤ u * ‖x‖^2 := by
  have hlo := integral_mono (integrable_const l) (hψ x) hl
  have hup := integral_mono (hψ x) (integrable_const u) hu
  rw [integral_const, momentMeasure_mass A μ hμ] at hlo hup
  simpa only [smul_eq_mul, mul_comm, momentQuadraticValue] using And.intro hlo hup

/-- A strictly positive lower weight produces a genuine inner-product core. -/
def momentInnerCore (l u : ℝ) (hlpos : 0 < l)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) : InnerProductSpace.Core ℝ E where
  inner := fun x y => momentBilinear A μ hμ ψ hψ x y
  conj_symm x y := by
    simpa only [conj_trivial] using (momentBilinear_symmetric A μ hμ ψ hψ).eq y x
  nonneg_re x := by
    change 0 ≤ momentBilinear A μ hμ ψ hψ x x
    rw [momentBilinear_self]
    exact (mul_nonneg hlpos.le (sq_nonneg _)).trans (momentQuadratic_bounds A μ hμ ψ hψ l u hl hu x).1
  definite x hx := by
    change momentBilinear A μ hμ ψ hψ x x = 0 at hx
    rw [momentBilinear_self] at hx
    have h := (momentQuadratic_bounds A μ hμ ψ hψ l u hl hu x).1
    rw [hx] at h
    have hn : ‖x‖^2 ≤ 0 := by
      apply (mul_le_mul_left hlpos).mp
      simpa only [mul_zero] using h
    exact norm_eq_zero.mp (pow_eq_zero (le_antisymm hn (sq_nonneg _)))
  add_left x y z := (momentBilinear A μ hμ ψ hψ).map_add₂ x y z
  smul_left x y c := by
    simpa only [conj_trivial, smul_eq_mul] using (momentBilinear A μ hμ ψ hψ).map_smul₂ c x y


/-- Cauchy--Schwarz in the constructed core gives the original-norm bilinear bound. -/
theorem momentBilinear_bound (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) (x y : E) :
    ‖momentBilinear A μ hμ ψ hψ x y‖ ≤ u * ‖x‖ * ‖y‖ := by
  have hcs := @InnerProductSpace.Core.inner_mul_inner_self_le ℝ E _ _ _
    (momentInnerCore A μ hμ ψ hψ l u hlpos hl hu) x y
  change ‖momentBilinear A μ hμ ψ hψ x y‖ * ‖momentBilinear A μ hμ ψ hψ y x‖ ≤
    momentBilinear A μ hμ ψ hψ x x * momentBilinear A μ hμ ψ hψ y y at hcs
  rw [(momentBilinear_symmetric A μ hμ ψ hψ).eq y x,
    momentBilinear_self, momentBilinear_self] at hcs
  have hqx := momentQuadratic_bounds A μ hμ ψ hψ l u hl hu x
  have hqy := momentQuadratic_bounds A μ hμ ψ hψ l u hl hu y
  have hy0 : 0 ≤ momentQuadraticValue μ ψ y :=
    (mul_nonneg hlpos.le (sq_nonneg _)).trans hqy.1
  have hprod := mul_le_mul hqx.2 hqy.2 hy0 (mul_nonneg hu0 (sq_nonneg _))
  apply nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (mul_nonneg hu0 (norm_nonneg _)) (norm_nonneg _))
  calc
    ‖momentBilinear A μ hμ ψ hψ x y‖ * ‖momentBilinear A μ hμ ψ hψ x y‖ ≤
        momentQuadraticValue μ ψ x * momentQuadraticValue μ ψ y := hcs
    _ ≤ (u * ‖x‖^2) * (u * ‖y‖^2) := hprod
    _ = (u * ‖x‖ * ‖y‖) * (u * ‖x‖ * ‖y‖) := by ring

/-- The weighted form is bounded in the original Hilbert norm. -/
def momentBilinearContinuous (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) : E →L[ℝ] E →L[ℝ] ℝ :=
  (momentBilinear A μ hμ ψ hψ).mkContinuous₂ u
    (momentBilinear_bound A μ hμ ψ hψ l u hlpos hu0 hl hu)

/-- Hilbert Riesz constructs the actual bounded operator representing the Borel form. -/
def momentOperator [CompleteSpace E] (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) : E →L[ℝ] E :=
  InnerProductSpace.continuousLinearMapOfBilin
    (momentBilinearContinuous A μ hμ ψ hψ l u hlpos hu0 hl hu)

theorem momentOperator_inner [CompleteSpace E] (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) (x y : E) :
    ⟪momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x, y⟫ =
      momentBilinear A μ hμ ψ hψ x y :=
  InnerProductSpace.continuousLinearMapOfBilin_apply _ x y

theorem momentOperator_self [CompleteSpace E] (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) (x : E) :
    ⟪momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x, x⟫ =
      ∫ t, ψ t ∂(μ x : Measure (Icc a b)) := by
  rw [momentOperator_inner, momentBilinear_self]
  rfl

theorem momentOperator_symmetric [CompleteSpace E] (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) :
    (momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu).toLinearMap.IsSymmetric := by
  intro x y
  change ⟪momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x, y⟫ =
    ⟪x, momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu y⟫
  rw [real_inner_comm (momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu y) x,
    momentOperator_inner, momentOperator_inner]
  exact (momentBilinear_symmetric A μ hμ ψ hψ).eq x y

theorem momentOperator_bounds [CompleteSpace E] (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) (x : E) :
    l * ‖x‖^2 ≤ ⟪x, momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x⟫ ∧
      ⟪x, momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x⟫ ≤ u * ‖x‖^2 := by
  rw [real_inner_comm (momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x) x, momentOperator_self]
  exact momentQuadratic_bounds A μ hμ ψ hψ l u hl hu x

/-- The operator commutation law follows from a finite scalar moment identity. -/
theorem momentBilinear_commute (hA : A.toLinearMap.IsSymmetric) (x y : E) :
    momentBilinear A μ hμ ψ hψ (A x) y = momentBilinear A μ hμ ψ hψ x (A y) := by
  have hrel := integral_relation_of_moments a b
    (fun i : Fin 6 => μ (![A x+y, A x, y, x+A y, x, A y] i))
    (![1, -1, -1, -1, 1, 1])
    (by
      intro k
      norm_num [Fin.sum_univ_succ, hμ, operator_iterate_add, inner_add_left, inner_add_right]
      have hxy : ⟪A x, (A : E → E)^[k] y⟫ = ⟪x, (A : E → E)^[k] (A y)⟫ := by
        calc
          _ = ⟪x, A ((A : E → E)^[k] y)⟫ := hA _ _
          _ = _ := congrArg (fun z : E => ⟪x, z⟫)
            ((Function.iterate_succ_apply' (A : E → E) k y).symm.trans
              (Function.iterate_succ_apply (A : E → E) k y))
      have hyx : ⟪A y, (A : E → E)^[k] x⟫ = ⟪y, (A : E → E)^[k] (A x)⟫ := by
        calc
          _ = ⟪y, A ((A : E → E)^[k] x)⟫ := hA _ _
          _ = _ := congrArg (fun z : E => ⟪y, z⟫)
            ((Function.iterate_succ_apply' (A : E → E) k x).symm.trans
              (Function.iterate_succ_apply (A : E → E) k x))
      rw [hxy, hyx]
      ring)
    ψ (fun i => hψ _)
  norm_num [Fin.sum_univ_succ] at hrel
  rw [momentBilinear_apply, momentBilinear_apply]
  unfold momentQuadraticValue
  linarith only [hrel]

theorem momentOperator_commute [CompleteSpace E] (hA : A.toLinearMap.IsSymmetric)
    (l u : ℝ) (hlpos : 0 < l) (hu0 : 0 ≤ u)
    (hl : ∀ t, l ≤ ψ t) (hu : ∀ t, ψ t ≤ u) :
    Commute (momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu) A := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℝ
  intro y
  change ⟪momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu (A x), y⟫ =
    ⟪A (momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x), y⟫
  have hAy : ⟪A (momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x), y⟫ =
      ⟪momentOperator A μ hμ ψ hψ l u hlpos hu0 hl hu x, A y⟫ := hA _ _
  rw [hAy, momentOperator_inner, momentOperator_inner]
  exact momentBilinear_commute A μ hμ ψ hψ hA x y

end BB
