import BB.GradientDynamics
import BB.FiniteSharp

/-!
# Sharp rates for actual delayed diagonal BB1 gradient trajectories

The first gradient `g 1` is unrestricted in the root-factor theorem. Finite
termination is absorbed explicitly and no global nontermination hypothesis
appears in the final statements.
-/

namespace BB
noncomputable section
open Filter
open scoped Topology

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gradient_eventually_zero_of_zero (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1)))
    (k : ℕ) (hkpos : 0 < k) (hk : g k = 0) : ∀ᶠ n in atTop, g n = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  have hz := zero_gradient_stays_zero lam g hupdate j hk
  apply Filter.eventually_atTop.mpr
  refine ⟨j + 1, ?_⟩
  intro n hn
  have he : j + 1 + (n - (j + 1)) = n := by omega
  simpa only [he] using hz (n - (j + 1))

lemma gradient_eventual_envelope (lam : ι → ℝ) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hγ : rate A B < γ) (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ n in atTop, normDiag (g n) ≤ D * γ ^ n := by
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  by_cases hterm : ∃ k : ℕ, g k = 0
  · obtain ⟨k, hk⟩ := hterm
    have hkpos : 0 < k := by
      by_contra h
      have hk0 : k = 0 := by omega
      have he : energy (g 0) = 0 := (energy_eq_zero_iff _).mpr (hk0 ▸ hk)
      linarith
    refine ⟨1, zero_lt_one, ?_⟩
    filter_upwards [gradient_eventually_zero_of_zero lam g hupdate k hkpos hk] with n hn
    rw [hn]
    simp only [normDiag, energy, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero, one_mul]
    exact pow_nonneg hγpos.le n
  · have hg : ∀ n, 0 < energy (g n) := by
      intro n
      have hne : energy (g n) ≠ 0 := fun h => hterm ⟨n, (energy_eq_zero_iff _).mp h⟩
      exact lt_of_le_of_ne (energy_nonneg _) hne.symm
    obtain ⟨C, hC, henv⟩ := finite_spectral_envelope lam A B γ hA hAB hlam hγ
    have hg1 : 0 < normDiag (g 1) := Real.sqrt_pos.mpr (hg 1)
    let D := normDiag (g 1) * C / γ
    refine ⟨D, div_pos (mul_pos hg1 hC) hγpos, ?_⟩
    apply Filter.eventually_atTop.mpr
    refine ⟨1, ?_⟩
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    rw [gradient_orbit_norm_product lam g hg hupdate m]
    calc
      normDiag (g 1) * prefixProduct (stateGrowth lam) (spectralMap lam) m
          (normalizedPair (g 1) (g 0) (hg 1) (hg 0)) ≤
          normDiag (g 1) * (C * γ ^ m) :=
        mul_le_mul_of_nonneg_left (henv m _) hg1.le
      _ = D * γ ^ (m + 1) := by dsimp [D]; rw [pow_succ]; field_simp; ring

lemma gradient_rootFactor_le (lam : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n)) ≤ rate A B := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  obtain ⟨D, hD, henv⟩ := gradient_eventual_envelope lam A B γ hA hAB hlam hγ g hg0 hupdate
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  exact rootFactor_le_of_eventual_envelope (fun n => normDiag (g n))
    (fun n => norm_diag_nonneg _) D γ hD (hc0.trans hγ.le) henv

lemma gradient_rootTerm_bounded (lam : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => normDiag (g n))) := by
  obtain ⟨D, hD, henv⟩ := gradient_eventual_envelope lam A B (rate A B + 1)
    hA hAB hlam (by linarith) g hg0 hupdate
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  exact rootTerm_bounded_of_eventual_envelope (fun n => normDiag (g n))
    (fun n => norm_diag_nonneg _) D (rate A B + 1) hD (by linarith) henv

/-- The manuscript's normalized root-factor upper bound, including arbitrary
first steps and finite termination. -/
lemma gradient_normalized_rootFactor_le (lam : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ≤ rate A B := by
  rw [rootFactor_div_const (fun n => normDiag (g n)) (fun n => norm_diag_nonneg _)
    (gradient_rootTerm_bounded lam A B hA hAB hlam g hg0 hupdate) (normDiag (g 0))
    (Real.sqrt_pos.mpr hg0)]
  exact gradient_rootFactor_le lam A B hA hAB hlam g hg0 hupdate

/-- Finite-horizon normalized-state identity. Positivity is required only
through the stated horizon, not for the rest of the trajectory. -/
lemma gradient_orbit_state_iterates_up_to (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1)))
    (n : ℕ) : ∀ (hg : ∀ j, j ≤ n + 1 → 0 < energy (g j)),
    normalizedPair (g (n + 1)) (g n) (hg (n + 1) le_rfl) (hg n (by omega)) =
      (spectralMap lam)^[n] (normalizedPair (g 1) (g 0) (hg 1 (by omega)) (hg 0 (by omega))) := by
  induction n with
  | zero => intro hg; rfl
  | succ n ih =>
    intro hg
    have hg' : ∀ j, j ≤ n + 1 → 0 < energy (g j) := fun j hj => hg j (by omega)
    rw [normalized_pair_update (hg n (by omega)) (hg (n + 1) (by omega)) (hg (n + 2) (by omega)) (hupdate n),
      ih hg', Function.iterate_succ_apply']

lemma gradient_orbit_norm_product_up_to (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1)))
    (n : ℕ) : ∀ (hg : ∀ j, j ≤ n + 1 → 0 < energy (g j)),
    normDiag (g (n + 1)) = normDiag (g 1) *
      prefixProduct (stateGrowth lam) (spectralMap lam) n
        (normalizedPair (g 1) (g 0) (hg 1 (by omega)) (hg 0 (by omega))) := by
  induction n with
  | zero => intro _hg; simp
  | succ n ih =>
    intro hg
    have hg' : ∀ j, j ≤ n + 1 → 0 < energy (g j) := fun j hj => hg j (by omega)
    have hstep : normDiag (g (n + 2)) =
        stateGrowth lam (normalizedPair (g (n + 1)) (g n) (hg (n + 1) (by omega)) (hg n (by omega))) *
          normDiag (g (n + 1)) := by
      rw [hupdate n, diagonal_bb1_reciprocal_mean]
      exact norm_update_factorization (hg (n + 1) (by omega))
    rw [hstep,
      gradient_orbit_state_iterates_up_to lam g hupdate n hg', ih hg']
    rw [prefix_product_cocycle (stateGrowth lam) (spectralMap lam) n 1]
    simp only [prefix_product_succ, prefix_product_zero, mul_one]
    ring

/-- A nonzero target gradient certifies positivity of every earlier gradient. -/
lemma gradient_positive_before_nonzero (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1)))
    (hg0 : 0 < energy (g 0)) (n : ℕ) (hn : g n ≠ 0) :
    ∀ j, j ≤ n → 0 < energy (g j) := by
  intro j hj
  by_cases hj0 : j = 0
  · simpa [hj0] using hg0
  · have hne : energy (g j) ≠ 0 := by
      intro he
      have hzj : g j = 0 := (energy_eq_zero_iff _).mp he
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hz := zero_gradient_stays_zero lam g hupdate k hzj (n - (k + 1))
      have hidx : k + 1 + (n - (k + 1)) = n := by omega
      exact hn (hidx ▸ hz)
    exact lt_of_le_of_ne (energy_nonneg _) hne.symm


/-- Uniform exponential estimate for all trajectories whose first gradient has
an a priori bound. The constant is independent of the particular trajectory. -/
lemma gradient_uniform_envelope_of_first_bound (lam : ι → ℝ) (A B γ M : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hγ : rate A B < γ) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → ι → ℝ), 0 < energy (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) →
      normDiag (g 1) ≤ M * normDiag (g 0) →
      ∀ n, normDiag (g n) ≤ K * γ ^ n * normDiag (g 0) := by
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  obtain ⟨C, hC, henv⟩ := finite_spectral_envelope lam A B γ hA hAB hlam hγ
  let D : ℝ := C * M / γ
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hC.le hM) hγpos.le
  refine ⟨1 + D, by linarith, ?_⟩
  intro g hg0 hupdate hfirst n
  by_cases hn0 : n = 0
  · subst n
    simp only [pow_zero, mul_one]
    nlinarith [norm_diag_nonneg (g 0)]
  · by_cases hn : g n = 0
    · rw [hn]
      simp only [normDiag, energy, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, Real.sqrt_zero]
      exact mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hγpos.le n))
        (norm_diag_nonneg _)
    · have hgpre := gradient_positive_before_nonzero lam g hupdate hg0 n hn
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
      rw [gradient_orbit_norm_product_up_to lam g hupdate m hgpre]
      calc
        normDiag (g 1) * prefixProduct (stateGrowth lam) (spectralMap lam) m
            (normalizedPair (g 1) (g 0) (hgpre 1 (by omega)) (hgpre 0 (by omega))) ≤
            normDiag (g 1) * (C * γ ^ m) :=
          mul_le_mul_of_nonneg_left (henv m _) (norm_diag_nonneg _)
        _ ≤ (M * normDiag (g 0)) * (C * γ ^ m) :=
          mul_le_mul_of_nonneg_right hfirst (mul_nonneg hC.le (pow_nonneg hγpos.le m))
        _ = D * γ ^ (m + 1) * normDiag (g 0) := by
          dsimp [D]
          rw [pow_succ]
          field_simp
          ring
        _ ≤ (1 + D) * γ ^ (m + 1) * normDiag (g 0) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hγpos.le _))
            (norm_diag_nonneg _)

lemma matched_first_gradient_bound (lam : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hfirst : g 1 = gradientUpdate lam (diagonalBB1 lam (g 0)) (g 0)) :
    normDiag (g 1) ≤ (1 + B / A) * normDiag (g 0) := by
  rw [hfirst, diagonal_bb1_reciprocal_mean, norm_update_factorization hg0]
  exact mul_le_mul_of_nonneg_right
    (state_growth_bound lam A B hA hAB hlam (normalizedPair (g 0) (g 0) hg0 hg0))
    (norm_diag_nonneg _)

/-- The matched-initialization uniform estimate, with one constant for all
initial gradients and including trajectories that terminate at any later step. -/
lemma gradient_matched_uniform_envelope (lam : ι → ℝ) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hγ : rate A B < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → ι → ℝ), 0 < energy (g 0) →
      g 1 = gradientUpdate lam (diagonalBB1 lam (g 0)) (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) →
      ∀ n, normDiag (g n) ≤ K * γ ^ n * normDiag (g 0) := by
  have hM : 0 ≤ 1 + B / A := by have hB : 0 < B := hA.trans_le hAB; positivity
  obtain ⟨K, hK, henv⟩ := gradient_uniform_envelope_of_first_bound lam A B γ (1 + B/A)
    hA hAB hlam hγ hM
  refine ⟨K, hK, ?_⟩
  intro g hg0 hfirst hupdate
  exact henv g hg0 hupdate (matched_first_gradient_bound lam A B hA hAB hlam g hg0 hfirst)

end
end BB
