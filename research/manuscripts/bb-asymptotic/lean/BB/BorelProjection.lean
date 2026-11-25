import BB.BorelSignedMeasure
import BB.BorelEigen

/-!
# Actual spectral projections from bounded Borel indicators

Every measurable spectral set gives a symmetric idempotent bounded operator.
Its diagonal, norm square and restriction of every actual scalar spectral
measure are proved, providing the literal projection spectral-measure bridge.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology ENNReal
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a * ‖x‖^2 ≤ ⟪x, A x⟫ ∧ ⟪x, A x⟫ ≤ b * ‖x‖^2)

lemma indicator_one_abs_bound (B : Set (Icc a b)) (t : Icc a b) :
    |B.indicator (fun _ => (1 : ℝ)) t| ≤ 1 := by
  classical
  by_cases ht : t ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_not_mem, ht]

/-- The actual spectral projection of an interval Borel set. -/
def spectralProjection (B : Set (Icc a b)) (hB : MeasurableSet B) : E →L[ℝ] E :=
  borelOperator A hA a b hbounds (B.indicator (fun _ => (1 : ℝ)))
    (measurable_const.indicator hB) 1 zero_le_one (indicator_one_abs_bound a b B)

theorem spectral_projection_symmetric (B : Set (Icc a b)) (hB : MeasurableSet B) :
    (spectralProjection A hA a b hbounds B hB).toLinearMap.IsSymmetric :=
  borel_operator_symmetric _ _ _ _ _ _ _ _ _ _

theorem spectral_projection_commute (B : Set (Icc a b)) (hB : MeasurableSet B) :
    Commute (spectralProjection A hA a b hbounds B hB) A :=
  borel_operator_commute _ _ _ _ _ _ _ _ _ _

/-- Literal diagonal scalar measure identity for the constructed projection. -/
theorem spectral_projection_self (B : Set (Icc a b)) (hB : MeasurableSet B) (x : E) :
    ⟪spectralProjection A hA a b hbounds B hB x, x⟫ =
      ((operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) B).toReal := by
  rw [spectralProjection, borel_operator_self, integral_indicator hB, integral_const]
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]

/-- The paper's exact projection-square scalar spectral-measure identity. -/
theorem spectral_projection_norm_sq (B : Set (Icc a b)) (hB : MeasurableSet B) (x : E) :
    ‖spectralProjection A hA a b hbounds B hB x‖^2 =
      ((operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) B).toReal := by
  rw [spectralProjection, borel_operator_norm_sq]
  have heq : (fun t => (B.indicator (fun _ => (1 : ℝ)) t)^2) = B.indicator (fun _ => (1 : ℝ)) := by
    classical
    funext t
    by_cases ht : t ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_not_mem, ht]
  rw [heq, integral_indicator hB, integral_const]
  simp only [Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul, mul_one]

/-- Projection restricts every actual scalar spectral measure to its Borel set. -/
theorem spectral_projection_measure (B : Set (Icc a b)) (hB : MeasurableSet B) (x : E) :
    (operatorSpectralMeasure A hA a b hbounds (spectralProjection A hA a b hbounds B hB x) :
      Measure (Icc a b)) =
      (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)).restrict B := by
  rw [spectralProjection, borel_operator_scalar_measure]
  change (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)).withDensity
      (fun t => ENNReal.ofReal ((B.indicator (fun _ => (1 : ℝ)) t)^2)) = _
  have heq : (fun t => ENNReal.ofReal ((B.indicator (fun _ => (1 : ℝ)) t)^2)) =
      B.indicator (fun _ => (1 : ℝ≥0∞)) := by
    classical
    funext t
    by_cases ht : t ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_not_mem, ht]
  rw [heq]
  exact withDensity_indicator_one hB

/-- The constructed projection is actually idempotent. -/
theorem spectral_projection_idempotent (B : Set (Icc a b)) (hB : MeasurableSet B) :
    (spectralProjection A hA a b hbounds B hB).comp (spectralProjection A hA a b hbounds B hB) =
      spectralProjection A hA a b hbounds B hB := by
  let P := spectralProjection A hA a b hbounds B hB
  have hP := spectral_projection_symmetric A hA a b hbounds B hB
  have hPP : (P.comp P).toLinearMap.IsSymmetric := by
    intro x y
    change ⟪P (P x), y⟫ = ⟪x, P (P y)⟫
    calc
      _ = ⟪P x, P y⟫ := hP _ _
      _ = _ := hP _ _
  apply symmetric_operator_eq_of_diagonal _ _ hPP hP
  intro x
  change ⟪P (P x), x⟫ = ⟪P x, x⟫
  calc
    _ = ⟪P x, P x⟫ := hP _ _
    _ = ‖P x‖^2 := real_inner_self_eq_norm_sq _
    _ = _ := (spectral_projection_norm_sq A hA a b hbounds B hB x).trans
      (spectral_projection_self A hA a b hbounds B hB x).symm

/-- Correct eigenvector action of the signed Borel construction. -/
theorem borel_operator_eigenvector (φ : Icc a b → ℝ) (hφ : Measurable φ)
    (C : ℝ) (hC : 0 ≤ C) (hφC : ∀ t, |φ t| ≤ C)
    (r : Icc a b) (x : E) (hx : A x = (r : ℝ) • x) :
    borelOperator A hA a b hbounds φ hφ C hC hφC x = φ r • x := by
  unfold borelOperator
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply,
    borel_weight_operator_eigenvector A hA a b hbounds (shiftedBorelWeight a b φ C)
      (shiftedBorelWeight_measurable a b φ hφ C) 1 (2*C+1) (by norm_num)
      (by linarith only [hC]) (shiftedBorelWeight_bounds a b φ C hφC) r x hx]
  rw [← sub_smul]
  congr 1
  dsimp [shiftedBorelWeight]
  ring

/-- A spectral projection retains exactly the eigenvectors whose value lies in its set. -/
theorem spectral_projection_eigenvector (B : Set (Icc a b)) (hB : MeasurableSet B)
    (r : Icc a b) (x : E) (hx : A x = (r : ℝ) • x) :
    spectralProjection A hA a b hbounds B hB x = B.indicator (fun _ => (1 : ℝ)) r • x :=
  borel_operator_eigenvector _ _ _ _ _ _ _ _ _ _ r x hx

end BB
