import BB.SpectralTopology
import BB.Lyapunov
import BB.CompactContraction

/-!
# Lyapunov certificates for the actual total BB state map

The terminal continuation is exactly `spectralMap` from `SpectralTopology`.
The local-mean version also applies on smaller invariant support faces.
The final rate-transfer lemma explicitly retains the boundary-prefix obligation.
-/

namespace BB
noncomputable section

variable {ι : Type*} [Fintype ι]

def stateLyapunov (a b : ℝ) (lo hi : ι) (χ : SpectralState ι) : ℝ :=
  endpointLyapunov a b lo hi χ.1.1

lemma state_lyapunov_nonneg (a b : ℝ) (lo hi : ι) (χ : SpectralState ι) :
    0 ≤ stateLyapunov a b lo hi χ :=
  endpointLyapunov_nonneg (χ.1.2.1 lo) (χ.1.2.1 hi)

lemma state_lyapunov_continuous {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (lo hi : ι) : Continuous (stateLyapunov a b lo hi) :=
  (endpointLyapunov_continuous ha hab lo hi).comp (continuous_subtype_val.comp continuous_fst)

lemma state_lyapunov_eq_zero_iff {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (lo hi : ι) (χ : SpectralState ι) :
    stateLyapunov a b lo hi χ = 0 ↔ χ.1.1 lo = 0 ∨ χ.1.1 hi = 0 :=
  endpointLyapunov_eq_zero_iff ha hab lo hi χ.1.1 (χ.1.2.1 lo) (χ.1.2.1 hi)

lemma state_growth_sq_identity (lam : ι → ℝ) (χ : SpectralState ι) :
    stateGrowth lam χ ^ 2 = stateGrowthSq lam χ :=
  Real.sq_sqrt (growth_sq_nonneg χ.1.2)

lemma state_lyapunov_step_of_mean_bounds {lam : ι → ℝ} {a b : ℝ} {lo hi : ι}
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (χ : SpectralState ι) (hmean : mean lam χ.2.1 ∈ Set.Icc a b) :
    stateGrowth lam χ ^ 2 * stateLyapunov a b lo hi (spectralMap lam χ) ≤
      rate a b ^ 2 * stateLyapunov a b lo hi χ := by
  rw [state_growth_sq_identity]
  by_cases hR : 0 < stateGrowthSq lam χ
  · have hmap := (spectral_map_regular lam χ hR).1
    unfold stateLyapunov
    rw [hmap]
    exact spectral_lyapunov_step_of_mean_bounds ha hab hlo hhi χ.1.2 hmean
  · have hRzero : stateGrowthSq lam χ = 0 :=
      le_antisymm (le_of_not_gt hR) (growth_sq_nonneg χ.1.2)
    rw [hRzero, zero_mul]
    exact mul_nonneg (sq_nonneg _) (state_lyapunov_nonneg a b lo hi χ)

lemma state_lyapunov_step {lam : ι → ℝ} {a b : ℝ} {lo hi : ι}
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (χ : SpectralState ι) :
    stateGrowth lam χ ^ 2 * stateLyapunov a b lo hi (spectralMap lam χ) ≤
      rate a b ^ 2 * stateLyapunov a b lo hi χ :=
  state_lyapunov_step_of_mean_bounds ha hab hlo hhi χ
    ⟨mean_lower χ.2.2 (fun i => (hlam i).1), mean_upper χ.2.2 (fun i => (hlam i).2)⟩

lemma spectral_prefix_lyapunov {lam : ι → ℝ} {a b : ℝ} {lo hi : ι}
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (n : ℕ) (χ : SpectralState ι) :
    prefixProduct (stateGrowth lam) (spectralMap lam) n χ ^ 2 *
        stateLyapunov a b lo hi ((spectralMap lam)^[n] χ) ≤
      (rate a b ^ 2) ^ n * stateLyapunov a b lo hi χ :=
  prefix_product_lyapunov (stateGrowth lam) (spectralMap lam) (stateLyapunov a b lo hi)
    (rate a b ^ 2) (sq_nonneg _) (state_lyapunov_step ha hab hlo hhi hlam) n χ

/-- Actual BB cocycle rate improvement conditional on the strictly smaller
support-face boundary estimate. No boundary estimate is postulated as an axiom. -/
lemma spectral_uniform_rate_of_boundary_prefix {lam : ι → ℝ} {a b γ : ℝ} {lo hi : ι}
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (hγ : rate a b < γ)
    (hboundary : ∀ χ : SpectralState ι, stateLyapunov a b lo hi χ = 0 →
      ∃ n : ℕ, 0 < n ∧ prefixProduct (stateGrowth lam) (spectralMap lam) n χ < γ ^ n) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < γ ∧
      ∀ n χ, prefixProduct (stateGrowth lam) (spectralMap lam) n χ ≤ C * ρ ^ n := by
  letI : Nonempty ι := ⟨lo⟩
  have hc : 0 < rate a b := rate_pos ha hab
  have hγpos : 0 < γ := hc.trans hγ
  apply compact_boundary_lyapunov_improved_rate (spectralMap lam)
    (prefixProduct (stateGrowth lam) (spectralMap lam))
    (fun χ => rfl) (spectral_prefix_continuous lam a b ha hab.le hlam)
    (prefix_product_nonneg (stateGrowth lam) (spectralMap lam) (state_growth_nonneg lam))
    (prefix_product_cocycle (stateGrowth lam) (spectralMap lam))
    (stateLyapunov a b lo hi) (state_lyapunov_continuous ha hab lo hi)
    (state_lyapunov_nonneg a b lo hi) (rate a b ^ 2) γ (sq_nonneg _) hγpos
    (by nlinarith) (spectral_prefix_lyapunov ha hab hlo hhi hlam) hboundary

end
end BB
