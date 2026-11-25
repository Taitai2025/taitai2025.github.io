import BB.NonlinearFinite
import BB.UniversalWeighted
import BB.PositiveOperator
import BB.FrozenCompression

/-!
# Uniform frozen envelopes in arbitrary real inner product spaces

The finite-dimensional constant is chosen before the dimension, spectrum,
operator and initial pair.  Exact compression of each finite actual trajectory
then proves the Hilbert-space envelope with that same constant.
-/

noncomputable section
namespace BB.Nonlinear

universe u

def Rule.weightPower (rule : Rule) : ℕ := match rule with | .long => 2 | .short => 3

/-- Uniformity before dimension is essential for exact finite compression. -/
theorem universal_finite_frozen_envelope (rule : Rule) (m M β : ℝ)
    (hm : 0 < m) (hmM : m ≤ M) (hβ : rate m M < β) :
    ∃ C ≥ 1, ∀ {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] (A : E →L[ℝ] E),
      A.toLinearMap.IsSymmetric → PositiveModel A m M → QuadraticEnvelope rule A β C := by
  classical
  have hM : 0 < M := hm.trans_le hmM
  have hβ0 : 0 < β := (div_nonneg (sub_nonneg.mpr hmM) (add_nonneg hM.le hm.le)).trans_lt hβ
  have hL : 0 ≤ 1 + M / m := by positivity
  obtain ⟨K, _hK, henv⟩ := uniform_weighted_gradient_envelope m M β (1 + M / m)
    (m ^ rule.weightPower) (M ^ rule.weightPower) hm hmM hβ hL
    (pow_pos hm _) (pow_pos hM _)
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro E _ _ _ A hA h p x hpx n
  have hbounds : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) v (A v) ∧
      inner (𝕜 := ℝ) v (A v) ≤ M * ‖v‖ ^ 2 :=
    fun v => ⟨h.coercive v, inner_model_upper A M h.norm_upper v⟩
  have hlam := eigenvalue_bounds hA m M hbounds
  have hlo : ∀ i, m ^ rule.weightPower ≤ rule.errorWeight (eigenValues hA) i := by
    intro i
    cases rule <;> exact pow_le_pow_left hm.le (hlam i).1 _
  have hhi : ∀ i, rule.errorWeight (eigenValues hA) i ≤ M ^ rule.weightPower := by
    intro i
    cases rule <;> exact pow_le_pow_left (hm.le.trans (hlam i).1) (hlam i).2 _
  by_cases hx : x = 0
  · subst x
    simp only [bbCurrent_zero_initial rule A (map_zero A), norm_zero, mul_zero, le_refl]
  · let g : ℕ → Fin (FiniteDimensional.finrank ℝ E) → ℝ :=
      fun k => eigenCoordinates hA (bbCurrent rule A p x k)
    have hg0 : 0 < energy (g 0) := by
      dsimp [g]
      rw [eigen_coordinates_energy]
      exact sq_pos_of_pos (norm_pos_iff.mpr hx)
    have hupdate : ∀ k, g (k + 2) = gradientUpdate (eigenValues hA)
        (weightedBB (eigenValues hA) (rule.errorWeight (eigenValues hA)) (g k)) (g (k + 1)) := by
      intro k
      dsimp [g]
      rw [h.quadratic_delayed_update rule p x hpx k]
      change eigenCoordinates hA (operatorGradientStep A.toLinearMap _ _) = _
      rw [eigen_coordinates_update, eigen_coordinates_error_quotient]
    have hfirst : normDiag (g 1) ≤ (1 + M / m) * normDiag (g 0) := by
      dsimp [g]
      simpa only [eigen_coordinates_norm, bbCurrent_zero, pow_one] using
        h.quadratic_growth rule p x hpx 1
    have he := henv (FiniteDimensional.finrank ℝ E) (eigenValues hA)
      (rule.errorWeight (eigenValues hA)) hlam hlo hhi g hg0 hupdate hfirst n
    simp only [g, eigen_coordinates_norm, bbCurrent_zero] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K 1) (pow_nonneg hβ0.le n)) (norm_nonneg x))

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Actual frozen BB1/BB2 error envelopes in a real Hilbert space, uniform in
both initial points and independent of any finite-dimensional approximation. -/
theorem hilbert_frozen_envelope (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (rule : Rule) (m M β : ℝ) (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M * ‖z‖ ^ 2)
    (hβ : rate m M < β) : ∃ C ≥ 1, QuadraticEnvelope rule A β C := by
  obtain ⟨C, hC, hfinite⟩ := universal_finite_frozen_envelope.{u} rule m M β hm hmM hβ
  refine ⟨C, hC, ?_⟩
  intro p x hpx n
  let V := frozenCompressionSpace rule A p x n
  let B := operatorCompression A V
  have hB : B.toLinearMap.IsSymmetric := compression_symmetric A hA V
  have hboundsB := compression_bounds A V m M hbounds
  have hmodel : PositiveModel B m M := positiveModel_of_order_bounds B hB m M hm hmM hboundsB
  have hpne : frozenCompressionPrevious rule A p x n ≠ frozenCompressionInitial rule A p x n := by
    intro he
    apply hpx
    exact congrArg Subtype.val he
  have he := hfinite B hB hmodel (frozenCompressionPrevious rule A p x n)
    (frozenCompressionInitial rule A p x n) hpne n
  rw [frozen_compression_norm rule A p x n n le_rfl] at he
  exact he

end BB.Nonlinear
