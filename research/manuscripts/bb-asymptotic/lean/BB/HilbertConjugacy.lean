import BB.HilbertRates
import BB.HilbertWeightedSharpness

/-!
# Bounded positive-weight conjugacy on real Hilbert spaces

The square-root operator is an actual bounded operator: symmetry, commutation,
its square and its norm bounds are explicit hypotheses.  All quotient,
trajectory, root-factor and prefactor conclusions are proved from them.
Constructing this operator from an arbitrary Borel function is a separate
functional-calculus realization obligation.
-/

namespace BB
noncomputable section
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem operator_weighted_quotient_conjugacy (A W S : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) (hsquare : W = S.comp S)
    (hcomm : ∀ x, S (A x) = A (S x)) (x : E) :
    operatorWeightedBB A.toLinearMap W.toLinearMap x = operatorBB1 A.toLinearMap (S x) := by
  have hn : inner (𝕜 := ℝ) x (W x) = ‖S x‖^2 := by
    rw [hsquare]
    change inner (𝕜 := ℝ) x (S (S x)) = ‖S x‖^2
    calc
      inner (𝕜 := ℝ) x (S (S x)) = inner (𝕜 := ℝ) (S x) (S x) :=
        (hS x (S x)).symm
      _ = ‖S x‖^2 := real_inner_self_eq_norm_sq (S x)
  have hd : inner (𝕜 := ℝ) x (W (A x)) = inner (𝕜 := ℝ) (S x) (A (S x)) := by
    rw [hsquare]
    change inner (𝕜 := ℝ) x (S (S (A x))) = _
    calc
      inner (𝕜 := ℝ) x (S (S (A x))) = inner (𝕜 := ℝ) (S x) (S (A x)) :=
        (hS x (S (A x))).symm
      _ = inner (𝕜 := ℝ) (S x) (A (S x)) := by rw [hcomm x]
  change inner (𝕜 := ℝ) x (W x)/inner (𝕜 := ℝ) x (W (A x)) =
    ‖S x‖^2/inner (𝕜 := ℝ) (S x) (A (S x))
  rw [hn,hd]

theorem commuting_operator_step (A S : E →L[ℝ] E)
    (hcomm : ∀ x, S (A x) = A (S x)) (α : ℝ) (x : E) :
    S (operatorGradientStep A.toLinearMap α x) = operatorGradientStep A.toLinearMap α (S x) := by
  change S (x-α • A x) = S x-α • A (S x)
  rw [map_sub,map_smul,hcomm x]

theorem operator_weighted_orbit_conjugacy (A W S : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) (hsquare : W = S.comp S)
    (hcomm : ∀ x, S (A x) = A (S x)) (g : ℕ → E)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) :
    ∀ n, S (g (n+2)) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (S (g n))) (S (g (n+1))) := by
  intro n
  rw [hupdate n,commuting_operator_step A S hcomm,
    operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]

theorem norm_lower_operator_ne_zero (S : E →L[ℝ] E) (s : ℝ) (hs : 0 < s)
    (hlower : ∀ x, s*‖x‖ ≤ ‖S x‖) (x : E) (hx : x ≠ 0) : S x ≠ 0 := by
  apply norm_pos_iff.mp
  exact (mul_pos hs (norm_pos_iff.mpr hx)).trans_le (hlower x)

theorem hilbert_orbit_rootTerm_bounded (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => ‖g n‖)) := by
  have hn0 : 0 < ‖g 0‖ := norm_pos_iff.mpr hg0
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  let L : ℝ := ‖g 1‖/‖g 0‖
  have hL : 0 ≤ L := div_nonneg (norm_nonneg _) hn0.le
  have hfirst : ‖g 1‖ ≤ L*‖g 0‖ := by dsimp [L]; rw [div_mul_cancel₀ _ hn0.ne']
  obtain ⟨K,hK,henv⟩ := hilbert_common_uniform_envelope a b (rate a b+1) L ha hab (by linarith) hL
  apply rootTerm_bounded_of_eventual_envelope (fun n => ‖g n‖) (fun n => norm_nonneg _)
    (K*‖g 0‖) (rate a b+1) (mul_pos hK hn0) (by linarith)
  apply eventually_of_forall
  intro n
  simpa only [mul_assoc,mul_comm,mul_left_comm] using henv E A hA hbounds g hg0 hupdate hfirst n

theorem hilbert_weighted_root_conjugacy (A W S : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : W = S.comp S) (hcomm : ∀ x, S (A x) = A (S x))
    (a b s t : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) (ht : 0 < t)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (hSlower : ∀ x, s*‖x‖ ≤ ‖S x‖) (hSupper : ∀ x, ‖S x‖ ≤ t*‖x‖)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) = rootFactor (fun n => ‖S (g n)‖/‖S (g 0)‖) := by
  have hs0 := norm_lower_operator_ne_zero S s hs hSlower (g 0) hg0
  have hbS := hilbert_orbit_rootTerm_bounded A hA a b ha hab hbounds (fun n => S (g n)) hs0
    (operator_weighted_orbit_conjugacy A W S hS hsquare hcomm g hupdate)
  have hcomp : ∀ n, ‖g n‖ ≤ s⁻¹*‖S (g n)‖ := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hSlower (g n)) (inv_pos.mpr hs).le
    simpa only [← mul_assoc,inv_mul_cancel hs.ne',one_mul] using h
  have hbg := rootTerm_bounded_of_comparison (fun n => ‖g n‖) (fun n => ‖S (g n)‖)
    (fun n => norm_nonneg _) (fun n => norm_nonneg _) hbS s⁻¹ (inv_pos.mpr hs)
    (eventually_of_forall hcomp)
  rw [rootFactor_div_const _ (fun n => norm_nonneg _) hbg _ (norm_pos_iff.mpr hg0),
    rootFactor_div_const _ (fun n => norm_nonneg _) hbS _ (norm_pos_iff.mpr hs0)]
  exact rootFactor_eq_of_comparable (fun n => ‖g n‖) (fun n => ‖S (g n)‖)
    (fun n => norm_nonneg _) (fun n => norm_nonneg _) hbS s⁻¹ t (inv_pos.mpr hs) ht
    (eventually_of_forall hcomp) (eventually_of_forall (fun n => hSupper (g n)))

theorem hilbert_weighted_rootFactor_le (A W S : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : W = S.comp S) (hcomm : ∀ x, S (A x) = A (S x))
    (a b s t : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) (ht : 0 < t)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (hSlower : ∀ x, s*‖x‖ ≤ ‖S x‖) (hSupper : ∀ x, ‖S x‖ ≤ t*‖x‖)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤ rate a b := by
  rw [hilbert_weighted_root_conjugacy A W S hA hS hsquare hcomm a b s t ha hab hs ht
    hbounds hSlower hSupper g hg0 hupdate]
  exact hilbert_normalized_rootFactor_le A hA a b ha hab hbounds (fun n => S (g n))
    (norm_lower_operator_ne_zero S s hs hSlower (g 0) hg0)
    (operator_weighted_orbit_conjugacy A W S hS hsquare hcomm g hupdate)

/-- The norm-comparison prefactor is exactly t/s. -/
theorem hilbert_weighted_matched_envelope (A W S : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (hS : S.toLinearMap.IsSymmetric)
    (hsquare : W = S.comp S) (hcomm : ∀ x, S (A x) = A (S x))
    (a b s t γ : ℝ) (ha : 0 < a) (hab : a ≤ b) (hs : 0 < s) (_ht : 0 < t)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (hSlower : ∀ x, s*‖x‖ ≤ ‖S x‖) (hSupper : ∀ x, ‖S x‖ ≤ t*‖x‖)
    (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → E), g 0 ≠ 0 →
      g 1 = operatorGradientStep A.toLinearMap
        (operatorWeightedBB A.toLinearMap W.toLinearMap (g 0)) (g 0) →
      (∀ n, g (n+2) = operatorGradientStep A.toLinearMap
        (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) →
      ∀ n, ‖g n‖ ≤ (t/s)*K*γ^n*‖g 0‖ := by
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hγpos : 0 < γ := hc.trans_lt hγ
  obtain ⟨K,hK,henv⟩ := hilbert_matched_uniform_envelope A hA a b γ ha hab hbounds hγ
  refine ⟨K,hK,?_⟩
  intro g hg0 hfirst hupdate n
  have hs0 := norm_lower_operator_ne_zero S s hs hSlower (g 0) hg0
  have hsfirst : S (g 1) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (S (g 0))) (S (g 0)) := by
    rw [hfirst,commuting_operator_step A S hcomm,
      operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
  have he := henv (fun n => S (g n)) hs0 hsfirst
    (operator_weighted_orbit_conjugacy A W S hS hsquare hcomm g hupdate) n
  have hl : ‖g n‖ ≤ s⁻¹*‖S (g n)‖ := by
    have h := mul_le_mul_of_nonneg_left (hSlower (g n)) (inv_pos.mpr hs).le
    simpa only [← mul_assoc,inv_mul_cancel hs.ne',one_mul] using h
  calc
    ‖g n‖ ≤ s⁻¹*‖S (g n)‖ := hl
    _ ≤ s⁻¹*(K*γ^n*‖S (g 0)‖) := mul_le_mul_of_nonneg_left he (inv_pos.mpr hs).le
    _ ≤ s⁻¹*(K*γ^n*(t*‖g 0‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hSupper (g 0)) (mul_nonneg hK.le (pow_nonneg hγpos.le n)))
      (inv_pos.mpr hs).le
    _ = (t/s)*K*γ^n*‖g 0‖ := by ring

/-- Transfer any already valid BB1 envelope constant, rather than replacing
it by another constant for an equivalent Hilbert norm. -/
theorem hilbert_weighted_given_envelope_transfer (A W S : E →L[ℝ] E)
    (hS : S.toLinearMap.IsSymmetric) (hsquare : W = S.comp S)
    (hcomm : ∀ x, S (A x) = A (S x)) (s t C γ : ℝ)
    (hs : 0 < s) (hγ : 0 < γ)
    (hSlower : ∀ x, s*‖x‖ ≤ ‖S x‖) (hSupper : ∀ x, ‖S x‖ ≤ t*‖x‖)
    (henv : ∀ (v : ℕ → E), v 0 ≠ 0 →
      v 1 = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (v 0)) (v 0) →
      (∀ n, v (n+2) = operatorGradientStep A.toLinearMap
        (operatorBB1 A.toLinearMap (v n)) (v (n+1))) →
      ∀ n, ‖v n‖ ≤ C*γ^n*‖v 0‖)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W.toLinearMap (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W.toLinearMap (g n)) (g (n+1))) :
    ∀ n, ‖g n‖ ≤ (t/s)*C*γ^n*‖g 0‖ := by
  have hs0 := norm_lower_operator_ne_zero S s hs hSlower (g 0) hg0
  have hsf : S (g 1) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (S (g 0))) (S (g 0)) := by
    rw [hfirst, commuting_operator_step A S hcomm,
      operator_weighted_quotient_conjugacy A W S hS hsquare hcomm]
  have he := henv (fun n => S (g n)) hs0 hsf
    (operator_weighted_orbit_conjugacy A W S hS hsquare hcomm g hupdate)
  have hC : 0 ≤ C := by
    have hzero := he 0
    simp only [pow_zero, mul_one] at hzero
    have hpos := norm_pos_iff.mpr hs0
    nlinarith
  intro n
  have hl : ‖g n‖ ≤ s⁻¹*‖S (g n)‖ := by
    have h := mul_le_mul_of_nonneg_left (hSlower (g n)) (inv_pos.mpr hs).le
    simpa only [← mul_assoc, inv_mul_cancel hs.ne', one_mul] using h
  calc
    ‖g n‖ ≤ s⁻¹*‖S (g n)‖ := hl
    _ ≤ s⁻¹*(C*γ^n*‖S (g 0)‖) := mul_le_mul_of_nonneg_left (he n) (inv_pos.mpr hs).le
    _ ≤ s⁻¹*(C*γ^n*(t*‖g 0‖)) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (hSupper (g 0)) (mul_nonneg hC (pow_nonneg hγ.le n)))
      (inv_pos.mpr hs).le
    _ = (t/s)*C*γ^n*‖g 0‖ := by ring

end
end BB
