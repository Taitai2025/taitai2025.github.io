import BB.HilbertApproxOrbit
import BB.HilbertApproxBB2

/-!
# The literal infimum over rates in `(0,1)`

The unrestricted positive-rate greatest-lower-bound results imply the exact
interval-restricted infima written in the manuscript. In particular the upper
endpoint `1` is not silently included in the admissible set.
-/

noncomputable section
namespace BB
open Set

lemma positive_rate_window_isGLB {U : Set ℝ} {c : ℝ}
    (hpositive : ∀ γ ∈ U, 0 < γ) (hglb : IsGLB U c) (hc : c < 1) :
    IsGLB (U ∩ Ioo 0 1) c := by
  constructor
  · intro γ hγ
    exact hglb.1 hγ.1
  · intro x hx
    by_contra hn
    have hcx : c < x := lt_of_not_ge hn
    have hmin : min x 1 ∈ lowerBounds U := by
      intro γ hγ
      by_cases hγ1 : γ < 1
      · exact (min_le_left x 1).trans (hx ⟨hγ,hpositive γ hγ,hγ1⟩)
      · exact (min_le_right x 1).trans (le_of_not_gt hγ1)
    exact (not_lt_of_ge (hglb.2 hmin)) (lt_min hcx hc)

lemma rate_window_nonempty {U : Set ℝ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c < 1) (hupper : ∀ γ, c < γ → γ ∈ U) :
    (U ∩ Ioo 0 1).Nonempty := by
  refine ⟨(c+1)/2,hupper _ (by linarith),?_⟩
  exact ⟨by linarith,by linarith⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem hilbert_matched_uniform_rate_inf (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    sInf (MatchedOperatorUniformRates A ∩ Ioo 0 1) = rate a b := by
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hc1 := rate_lt_one ha hab
  have hupper : ∀ γ, rate a b < γ → γ ∈ MatchedOperatorUniformRates A := by
    intro γ hγ
    obtain ⟨C,hC,henv⟩ := hilbert_matched_uniform_envelope A hA a b γ ha hab hbounds hγ
    refine ⟨hc0.trans_lt hγ,C,hC,?_⟩
    intro x hx k
    exact henv (matchedOperatorOrbit A x) hx (matchedOperatorOrbit_one A x)
      (matchedOperatorOrbit_update A x) k
  exact (positive_rate_window_isGLB (fun _ hγ => hγ.1)
    (hilbert_matched_uniform_rates_isGLB A hA a b ha hab hbounds haspec hbspec) hc1).csInf_eq
      (rate_window_nonempty hc0 hc1 hupper)

theorem hilbert_bb2_matched_uniform_rate_inf (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    sInf (MatchedBB2UniformRates A ∩ Ioo 0 1) = rate a b := by
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hc1 := rate_lt_one ha hab
  have hupper : ∀ γ, rate a b < γ → γ ∈ MatchedBB2UniformRates A := by
    intro γ hγ
    obtain ⟨C,hC,henv⟩ := bb2_matched_uniform_family_envelope a b γ ha hab hγ
    refine ⟨hc0.trans_lt hγ,C,hC,?_⟩
    intro x hx k
    exact henv E A hA hbounds (matchedBB2Orbit A x) hx (matchedBB2Orbit_one A x)
      (matchedBB2Orbit_update A x) k
  exact (positive_rate_window_isGLB (fun _ hγ => hγ.1)
    (hilbert_bb2_matched_uniform_rates_isGLB A hA a b ha hab hbounds haspec hbspec) hc1).csInf_eq
      (rate_window_nonempty hc0 hc1 hupper)

end BB
