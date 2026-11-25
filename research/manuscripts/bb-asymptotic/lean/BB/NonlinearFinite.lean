import BB.NonlinearConvergence
import BB.LinearRates
import BB.WeightedRates

/-!
# Discharging the quadratic input in finite-dimensional Hilbert spaces

Both fixed BB rules are reduced to the already proved finite spectral theorem.
The incoming secant is arbitrary and the envelope constant is independent of
both initial points.  Thus the nonlinear conclusion here has no unproved
quadratic-envelope hypothesis.
-/

noncomputable section

namespace BB.Nonlinear

open scoped BigOperators Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Positive spectral conjugacy also transfers arbitrary bounded first steps. -/
theorem weighted_uniform_envelope_of_first_bound
    (lam ψ : ι → ℝ) (a b γ L : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hψ : ∀ i, 0 < ψ i) (hγ : rate a b < γ) (hL : 0 ≤ L) :
    ∃ K : ℝ, 0 < K ∧ ∀ g : ℕ → ι → ℝ, 0 < energy (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) →
      normDiag (g 1) ≤ L * normDiag (g 0) →
      ∀ n, normDiag (g n) ≤ K * γ ^ n * normDiag (g 0) := by
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hγpos : 0 < γ := hc.trans_lt hγ
  obtain ⟨s, t, hs, ht, hlo, hhi⟩ := positive_weights_bounds ψ hψ
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  let L' := Real.sqrt t * L * (Real.sqrt s)⁻¹
  have hL' : 0 ≤ L' := mul_nonneg (mul_nonneg hst.le hL) (inv_nonneg.mpr hss.le)
  obtain ⟨C, hC, henv⟩ := gradient_uniform_envelope_of_first_bound lam a b γ L'
    ha hab hlam hγ hL'
  let K := (Real.sqrt s)⁻¹ * C * Real.sqrt t
  have hinv : 0 < (Real.sqrt s)⁻¹ := inv_pos.mpr hss
  refine ⟨K, mul_pos (mul_pos hinv hC) hst, ?_⟩
  intro g hg0 hupdate hfirst n
  have hfirst' : normDiag (spectralScale ψ (g 1)) ≤
      L' * normDiag (spectralScale ψ (g 0)) := by
    calc
      _ ≤ Real.sqrt t * normDiag (g 1) := (spectral_scale_norm_bounds ψ (g 1) s t hs hlo hhi).2
      _ ≤ Real.sqrt t * (L * normDiag (g 0)) := mul_le_mul_of_nonneg_left hfirst hst.le
      _ ≤ Real.sqrt t * (L * ((Real.sqrt s)⁻¹ * normDiag (spectralScale ψ (g 0)))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (norm_le_inverse_scale ψ (g 0) s t hs hlo hhi) hL) hst.le
      _ = L' * normDiag (spectralScale ψ (g 0)) := by dsimp [L']; ring
  have he := henv (fun k => spectralScale ψ (g k)) (spectral_scale_energy_pos ψ hψ hg0)
    (weighted_delayed_update_conjugacy lam ψ g (fun i => (hψ i).le) hupdate) hfirst' n
  calc
    _ ≤ (Real.sqrt s)⁻¹ * normDiag (spectralScale ψ (g n)) :=
      norm_le_inverse_scale ψ (g n) s t hs hlo hhi
    _ ≤ (Real.sqrt s)⁻¹ * (C * γ ^ n * normDiag (spectralScale ψ (g 0))) :=
      mul_le_mul_of_nonneg_left he hinv.le
    _ ≤ (Real.sqrt s)⁻¹ * (C * γ ^ n * (Real.sqrt t * normDiag (g 0))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spectral_scale_norm_bounds ψ (g 0) s t hs hlo hhi).2
          (mul_nonneg hC.le (pow_nonneg hγpos.le n))) hinv.le
    _ = K * γ ^ n * normDiag (g 0) := by dsimp [K]; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {A : E →L[ℝ] E} {m M : ℝ}

theorem frozenQuotient_smul (rule : Rule) (A : E →L[ℝ] E) (v : E)
    (c : ℝ) (hc : c ≠ 0) : frozenQuotient rule A (c • v) = frozenQuotient rule A v := by
  have hh := bb_smul v (A v) c hc
  cases rule with
  | long => simpa only [frozenQuotient, Rule.quotient, map_smul] using hh.1
  | short => simpa only [frozenQuotient, Rule.quotient, map_smul] using hh.2

/-- Eliminating the generated secant gives the actual delayed quadratic update,
including a trajectory that has already terminated. -/
theorem PositiveModel.quadratic_delayed_update (h : PositiveModel A m M)
    (rule : Rule) (p x : E) (hpx : p ≠ x) (n : ℕ) :
    bbCurrent rule A p x (n + 2) = bbCurrent rule A p x (n + 1) -
      frozenQuotient rule A (A (bbCurrent rule A p x n)) • A (bbCurrent rule A p x (n + 1)) := by
  by_cases hz : bbCurrent rule A p x n = 0
  · have hz1 := bb_zero_next rule A p x (map_zero A) n hz
    have hz2 := bb_zero_next rule A p x (map_zero A) (n + 1) hz1
    simp only [hz2, hz1, map_zero, smul_zero, sub_self]
  · have hs := h.quadratic_regular rule p x hpx n hz
    have ha := h.frozen_interval rule
      (bbCurrent rule A p x n - bbPrevious rule A p x n) hs
    have hapos : 0 < bbStep rule A p x n := by
      rw [quadratic_bbStep]
      exact (one_div_pos.mpr h.M_pos).trans_le ha.1
    rw [show n + 2 = (n + 1) + 1 by omega, bbCurrent_succ, quadratic_bbStep,
      bb_secant_succ, frozenQuotient_smul rule A _ _ (neg_ne_zero.mpr hapos.ne')]

variable [FiniteDimensional ℝ E]

/-- The error-coordinate weight is λ² for BB1 and λ³ for BB2. -/
def Rule.errorWeight (rule : Rule) (lam : ι → ℝ) : ι → ℝ :=
  match rule with
  | .long => fun i => lam i ^ 2
  | .short => fun i => lam i ^ 3

theorem Rule.errorWeight_pos (rule : Rule) (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) :
    ∀ i, 0 < rule.errorWeight lam i := by
  cases rule <;> intro i <;> exact pow_pos (hlam i) _

theorem eigen_coordinates_error_quotient (rule : Rule)
    (hA : A.toLinearMap.IsSymmetric) (e : E) :
    frozenQuotient rule A (A e) =
      weightedBB (eigenValues hA) (rule.errorWeight (eigenValues hA)) (eigenCoordinates hA e) := by
  have happly (v : E) (i : Fin (FiniteDimensional.finrank ℝ E)) :
      eigenCoordinates hA (A v) i = eigenValues hA i * eigenCoordinates hA v i :=
    eigen_coordinates_apply hA v i
  have hinnerA (v : E) : inner (𝕜 := ℝ) v (A v) =
      ∑ i, eigenValues hA i * (eigenCoordinates hA v i) ^ 2 := eigen_coordinates_inner hA v
  have hnorm : ‖A e‖ ^ 2 = ∑ i, (eigenValues hA i) ^ 2 * (eigenCoordinates hA e i) ^ 2 := by
    rw [← eigen_coordinates_energy hA]
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    rw [happly]
    ring
  have hinner : inner (𝕜 := ℝ) (A e) (A (A e)) =
      ∑ i, (eigenValues hA i) ^ 3 * (eigenCoordinates hA e i) ^ 2 := by
    rw [hinnerA]
    apply Finset.sum_congr rfl
    intro i _
    rw [happly]
    ring
  have hnorm2 : ‖A (A e)‖ ^ 2 =
      ∑ i, (eigenValues hA i) ^ 4 * (eigenCoordinates hA e i) ^ 2 := by
    rw [← eigen_coordinates_energy hA]
    unfold energy
    apply Finset.sum_congr rfl
    intro i _
    rw [happly, happly]
    ring
  cases rule with
  | long =>
    simp only [frozenQuotient, Rule.quotient, bb1, hnorm, hinner,
      weightedBB, weightedEnergy, Rule.errorWeight]
    congr 1
  | short =>
    simp only [frozenQuotient, Rule.quotient, bb2, hnorm2, hinner,
      weightedBB, weightedEnergy, Rule.errorWeight]
    congr 1

theorem PositiveModel.finite_quadratic_envelope (h : PositiveModel A m M)
    (hA : A.toLinearMap.IsSymmetric) (rule : Rule) (β : ℝ) (hβ : rate m M < β) :
    ∃ C ≥ 1, QuadraticEnvelope rule A β C := by
  classical
  have hbounds : ∀ v : E, m * ‖v‖ ^ 2 ≤ inner (𝕜 := ℝ) v (A v) ∧
      inner (𝕜 := ℝ) v (A v) ≤ M * ‖v‖ ^ 2 :=
    fun v => ⟨h.coercive v, inner_model_upper A M h.norm_upper v⟩
  have hlam := eigenvalue_bounds hA m M hbounds
  have hψ := rule.errorWeight_pos (eigenValues hA)
    (fun i => h.m_pos.trans_le (hlam i).1)
  have hL : 0 ≤ 1 + M / m := by
    have hm := h.m_pos
    have hM := h.M_pos
    positivity
  obtain ⟨K, _hK, henv⟩ := weighted_uniform_envelope_of_first_bound (eigenValues hA)
    (rule.errorWeight (eigenValues hA)) m M β (1 + M / m)
    h.m_pos h.m_le_M hlam hψ hβ hL
  have hβ0 : 0 < β := (div_nonneg (sub_nonneg.mpr h.m_le_M)
    (add_nonneg h.M_pos.le h.m_pos.le)).trans_lt hβ
  refine ⟨max K 1, le_max_right _ _, ?_⟩
  intro p x hpx n
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
    have he := henv g hg0 hupdate hfirst n
    simp only [g, eigen_coordinates_norm, bbCurrent_zero] at he
    exact he.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left K 1) (pow_nonneg hβ0.le n)) (norm_nonneg x))

/-- Finite-dimensional local nonlinear convergence with the quadratic rate
proved from the spectral theorem, for either fixed classical BB rule. -/
theorem PositiveModel.finite_local_convergence (h : PositiveModel A m M)
    (hA : A.toLinearMap.IsSymmetric) (rule : Rule) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (γ R : ℝ) (hγ : rate m M < γ) (hγ1 : γ < 1) (hR : 0 < R) :
    ∃ ρ > 0, ρ ≤ R ∧ ∃ K ≥ 1, ∀ p x : E,
      ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → (x = 0 ∨ p ≠ x) →
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ K * γ ^ n * ‖x‖) ∧
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ R) ∧
      (∀ n, bbCurrent rule G p x n ≠ 0 →
        bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
        G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) := by
  obtain ⟨β, hcβ, hβγ⟩ := exists_between hγ
  obtain ⟨C, hC, hquad⟩ := h.finite_quadratic_envelope hA rule β hcβ
  have hc : 0 ≤ rate m M := div_nonneg (sub_nonneg.mpr h.m_le_M)
    (add_nonneg h.M_pos.le h.m_pos.le)
  exact h.local_convergence_of_quadratic_envelope rule G hG hstrict β γ C R
    (hc.trans_lt hcβ) hβγ hγ1 hC hR hquad

/-- Sharp root bounds in the same fixed neighborhood as a prescribed local
envelope rate, for either actual finite-dimensional nonlinear BB rule. -/
theorem PositiveModel.finite_local_sharp_convergence (h : PositiveModel A m M)
    (hA : A.toLinearMap.IsSymmetric) (rule : Rule) (G : E → E)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (γ R : ℝ) (hγ : rate m M < γ) (hγ1 : γ < 1) (hR : 0 < R) :
    ∃ ρ > 0, ρ ≤ R ∧ ∃ K ≥ 1, ∀ p x : E,
      ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → (x = 0 ∨ p ≠ x) →
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ K * γ ^ n * ‖x‖) ∧
      (∀ n, ‖bbCurrent rule G p x n‖ ≤ R) ∧
      (∀ n, bbCurrent rule G p x n ≠ 0 →
        bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
        G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) ∧
      Filter.Tendsto (bbCurrent rule G p x) Filter.atTop (𝓝 0) ∧
      rootFactor (fun n => ‖bbCurrent rule G p x n‖ / ‖x‖) ≤ rate m M := by
  have hc : 0 ≤ rate m M := div_nonneg (sub_nonneg.mpr h.m_le_M)
    (add_nonneg h.M_pos.le h.m_pos.le)
  have hc1 : rate m M < 1 := by
    unfold rate
    exact (div_lt_one (add_pos h.M_pos h.m_pos)).mpr (by linarith [h.m_pos])
  exact h.local_sharp_convergence_of_quadratic_envelopes rule G hG hstrict
    (rate m M) γ R hc hc1 hγ hγ1 hR (h.finite_quadratic_envelope hA rule)

end BB.Nonlinear
