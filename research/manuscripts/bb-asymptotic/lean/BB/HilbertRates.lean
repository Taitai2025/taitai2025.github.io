import BB.FunctionalEmbedding
import BB.UniversalFinite

/-!
# Unconditional sharp upper rates on real Hilbert spaces

The constants are obtained from the compact functional-state theorem and are
uniform in the operator and the dimension.  Exact finite compression connects
that scalar theorem to actual vector trajectories, including finite termination.
No spectral-measure representation or quadratic convergence assumption is a
premise of the theorems in this file.
-/

universe u
namespace BB
noncomputable section

/-- A common envelope for arbitrary first gradients with a fixed norm bound. -/
theorem hilbert_common_uniform_envelope (a b γ L : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hγ : rate a b < γ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (A : E →L[ℝ] E), A.toLinearMap.IsSymmetric →
      (∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
        inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) →
      ∀ (g : ℕ → E), g 0 ≠ 0 →
      (∀ n, g (n+2) = operatorGradientStep A.toLinearMap
        (operatorBB1 A.toLinearMap (g n)) (g (n+1))) →
      ‖g 1‖ ≤ L*‖g 0‖ → ∀ n, ‖g n‖ ≤ K*γ^n*‖g 0‖ := by
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  obtain ⟨C,hC,hU⟩ := uniform_spectral_envelope_exists a b γ ha hab hγ
  have hK : 0 < 1+C*L/γ := by positivity
  refine ⟨1+C*L/γ,hK,?_⟩
  intro E _ _ A hA hbounds g hg0 hupdate hfirst n
  exact operator_envelope_from_universal_finite A hA a b C γ L hC hγpos hL hU
    hbounds g hg0 hupdate hfirst n

/-- The matched BB1 envelope is uniform over all real inner-product spaces and
all selfadjoint operators satisfying the same positive quadratic-form bounds. -/
theorem hilbert_matched_uniform_family (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      (A : E →L[ℝ] E), A.toLinearMap.IsSymmetric →
      (∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
        inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) →
      ∀ (g : ℕ → E), g 0 ≠ 0 →
      g 1 = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g 0)) (g 0) →
      (∀ n, g (n+2) = operatorGradientStep A.toLinearMap
        (operatorBB1 A.toLinearMap (g n)) (g (n+1))) →
      ∀ n, ‖g n‖ ≤ K*γ^n*‖g 0‖ := by
  have hb : 0 < b := ha.trans_le hab
  have hL : 0 ≤ 1+b/a := by positivity
  obtain ⟨K,hK,henv⟩ := hilbert_common_uniform_envelope.{u} a b γ (1+b/a) ha hab hγ hL
  refine ⟨K,hK,?_⟩
  intro E _ _ A hA hbounds g hg0 hfirst hupdate
  apply henv E A hA hbounds g hg0 hupdate
  rw [hfirst]
  exact matched_operator_first_bound A hA a b ha hab hbounds (g 0) hg0

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Arbitrary first steps, and even arbitrary first gradients, have the sharp
global upper root factor.  No nontermination hypothesis is required. -/
theorem hilbert_normalized_rootFactor_le (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤ rate a b := by
  have hg0pos : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  let L : ℝ := ‖g 1‖/‖g 0‖
  have hL : 0 ≤ L := div_nonneg (norm_nonneg _) hg0pos.le
  have hfirst : ‖g 1‖ ≤ L*‖g 0‖ := by dsimp [L]; rw [div_mul_cancel₀ _ hg0pos.ne']
  apply rootFactor_le_of_all_envelopes (fun n => ‖g n‖/‖g 0‖)
    (fun n => div_nonneg (norm_nonneg _) hg0pos.le) (rate a b) hc0
  intro γ hγ
  obtain ⟨K,hK,henv⟩ := hilbert_common_uniform_envelope.{u} a b γ L ha hab hγ hL
  refine ⟨K,hK,?_⟩
  intro n
  exact (div_le_iff hg0pos).mpr (henv E A hA hbounds g hg0 hupdate hfirst n)

theorem hilbert_matched_uniform_envelope (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → E), g 0 ≠ 0 →
      g 1 = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g 0)) (g 0) →
      (∀ n, g (n+2) = operatorGradientStep A.toLinearMap
        (operatorBB1 A.toLinearMap (g n)) (g (n+1))) →
      ∀ n, ‖g n‖ ≤ K*γ^n*‖g 0‖ := by
  obtain ⟨K,hK,henv⟩ := hilbert_matched_uniform_family.{u} a b γ ha hab hγ
  exact ⟨K,hK,henv E A hA hbounds⟩

end
end BB
