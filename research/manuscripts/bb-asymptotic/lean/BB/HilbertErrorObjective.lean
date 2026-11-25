import BB.ErrorObjectiveMain
import BB.HilbertConjugacy

/-! # Actual Hilbert error and objective root factors -/

namespace BB
noncomputable section
open Filter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem hilbert_error_objective_factors_of_root_bounded (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g e : ℕ → E) (hg0 : g 0 ≠ 0) (hgradient : ∀ n, g n = A (e n))
    (hbounded : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => ‖g n‖))) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = rootFactor (fun n => ‖g n‖/‖g 0‖) ∧
      rootFactor (fun n => operatorObjective A.toLinearMap (e n)/operatorObjective A.toLinearMap (e 0)) =
        (rootFactor (fun n => ‖g n‖/‖g 0‖))^2 := by
  apply compared_error_objective_root_factors (fun n => ‖g n‖) (fun n => ‖e n‖)
    (fun n => operatorObjective A.toLinearMap (e n)) a b ha (ha.trans_le hab)
    (fun n => norm_nonneg _) (fun n => norm_nonneg _) (norm_pos_iff.mpr hg0) _ _ hbounded
  · intro n
    dsimp only
    rw [hgradient n]
    exact operator_norm_bounds_via_compression A hA a b ha hab hbounds (e n)
  · intro n
    have h := hbounds (e n)
    change a/2*‖e n‖^2 ≤ inner (𝕜 := ℝ) (e n) (A (e n))/2 ∧
      inner (𝕜 := ℝ) (e n) (A (e n))/2 ≤ b/2*‖e n‖^2
    constructor <;> linarith [h.1,h.2]

theorem hilbert_bb1_error_objective_factors (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g e : ℕ → E) (hg0 : g 0 ≠ 0) (hgradient : ∀ n, g n = A (e n))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = rootFactor (fun n => ‖g n‖/‖g 0‖) ∧
      rootFactor (fun n => operatorObjective A.toLinearMap (e n)/operatorObjective A.toLinearMap (e 0)) =
        (rootFactor (fun n => ‖g n‖/‖g 0‖))^2 :=
  hilbert_error_objective_factors_of_root_bounded A hA a b ha hab hbounds g e hg0 hgradient
    (hilbert_orbit_rootTerm_bounded A hA a b ha hab hbounds g hg0 hupdate)

lemma hilbert_bb2_orbit_rootTerm_bounded (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB2 A.toLinearMap (g n)) (g (n+1))) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => ‖g n‖)) := by
  have hn0 : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  let L : ℝ := ‖g 1‖/‖g 0‖
  have hL : 0 ≤ L := div_nonneg (norm_nonneg _) hn0.le
  have hfirst : ‖g 1‖ ≤ L*‖g 0‖ := by dsimp [L]; rw [div_mul_cancel₀ _ hn0.ne']
  obtain ⟨K,hK,henv⟩ := bb2_uniform_family_envelope a b 1 L ha hab (rate_lt_one ha hab) hL
  apply rootTerm_bounded_of_eventual_envelope (fun n => ‖g n‖) (fun n => norm_nonneg _)
    (K*‖g 0‖) 1 (mul_pos hK hn0) zero_le_one
  exact eventually_of_forall (fun n => by
    simpa only [one_pow,mul_one] using henv E A hA hbounds g hg0 hupdate hfirst n)

theorem hilbert_bb2_error_objective_factors (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g e : ℕ → E) (hg0 : g 0 ≠ 0) (hgradient : ∀ n, g n = A (e n))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB2 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = rootFactor (fun n => ‖g n‖/‖g 0‖) ∧
      rootFactor (fun n => operatorObjective A.toLinearMap (e n)/operatorObjective A.toLinearMap (e 0)) =
        (rootFactor (fun n => ‖g n‖/‖g 0‖))^2 :=
  hilbert_error_objective_factors_of_root_bounded A hA a b ha hab hbounds g e hg0 hgradient
    (hilbert_bb2_orbit_rootTerm_bounded A hA a b ha hab hbounds g hg0 hupdate)

theorem hilbert_weighted_error_objective_factors (A W S : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : W = S.comp S) (hcomm : ∀ x, S (A x) = A (S x))
    (a b s : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (hSlower : ∀ x, s*‖x‖ ≤ ‖S x‖)
    (g e : ℕ → E) (hg0 : g 0 ≠ 0) (hgradient : ∀ n, g n = A (e n))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖e n‖/‖e 0‖) = rootFactor (fun n => ‖g n‖/‖g 0‖) ∧
      rootFactor (fun n => operatorObjective A.toLinearMap (e n)/operatorObjective A.toLinearMap (e 0)) =
        (rootFactor (fun n => ‖g n‖/‖g 0‖))^2 := by
  have hs0 := norm_lower_operator_ne_zero S s hs hSlower (g 0) hg0
  have hbS := hilbert_orbit_rootTerm_bounded A hA a b ha hab hbounds (fun n => S (g n)) hs0
    (operator_weighted_orbit_conjugacy A W S hS hsquare hcomm g hupdate)
  have hcomp : ∀ n, ‖g n‖ ≤ s⁻¹*‖S (g n)‖ := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hSlower (g n)) (inv_pos.mpr hs).le
    simpa only [← mul_assoc,inv_mul_cancel hs.ne',one_mul] using h
  exact hilbert_error_objective_factors_of_root_bounded A hA a b ha hab hbounds g e hg0 hgradient
    (rootTerm_bounded_of_comparison (fun n => ‖g n‖) (fun n => ‖S (g n)‖)
      (fun n => norm_nonneg _) (fun n => norm_nonneg _) hbS s⁻¹ (inv_pos.mpr hs)
      (eventually_of_forall hcomp))

end
end BB
