import BB.Weighted
import BB.SpectralTopology

/-! # Actual diagonal gradient trajectories and normalized states -/

namespace BB
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

theorem normDiag_eq_euclidean_norm (x : EuclideanSpace ℝ ι) :
    normDiag (fun i => x i) = ‖x‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [normDiag,energy,Real.norm_eq_abs,sq_abs]

theorem diagonal_bb1_reciprocal_mean (lam g : ι → ℝ) :
    diagonalBB1 lam g = 1 / mean lam (energyWeights g) := by
  have hm : mean lam (energyWeights g) = (∑ i, lam i*(g i)^2)/energy g := by
    unfold mean energyWeights
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hm,one_div_div]
  rfl

theorem norm_update_factorization {lam g z : ι → ℝ} (hg : 0 < energy g) :
    normDiag (gradientUpdate lam (1/mean lam z) g) =
      Real.sqrt (growthSq lam (energyWeights g) z) * normDiag g := by
  unfold normDiag
  rw [energy_update_factorization hg,
    Real.sqrt_mul (growth_sq_nonneg (energy_weights_simplex hg))]

def normalizedPair (g h : ι → ℝ) (hg : 0 < energy g) (hh : 0 < energy h) : SpectralState ι :=
  (⟨energyWeights g,energy_weights_simplex hg⟩,⟨energyWeights h,energy_weights_simplex hh⟩)

theorem normalized_pair_regular {lam old cur next : ι → ℝ}
    (hold : 0 < energy old) (hcur : 0 < energy cur) (hnext : 0 < energy next)
    (hupdate : next = gradientUpdate lam (diagonalBB1 lam old) cur) :
    0 < stateGrowthSq lam (normalizedPair cur old hcur hold) := by
  have he : energy next = growthSq lam (energyWeights cur) (energyWeights old) * energy cur := by
    rw [hupdate,diagonal_bb1_reciprocal_mean]
    exact energy_update_factorization hcur
  change 0 < growthSq lam (energyWeights cur) (energyWeights old)
  have hnonneg := growth_sq_nonneg (lam := lam) (z := energyWeights old) (energy_weights_simplex hcur)
  by_contra hnot
  have hz : growthSq lam (energyWeights cur) (energyWeights old) = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  rw [hz,zero_mul] at he
  linarith

theorem normalized_pair_update {lam old cur next : ι → ℝ}
    (hold : 0 < energy old) (hcur : 0 < energy cur) (hnext : 0 < energy next)
    (hupdate : next = gradientUpdate lam (diagonalBB1 lam old) cur) :
    normalizedPair next cur hnext hcur = spectralMap lam (normalizedPair cur old hcur hold) := by
  have hR := normalized_pair_regular hold hcur hnext hupdate
  apply Prod.ext
  · apply Subtype.ext
    rw [(spectral_map_regular lam _ hR).1]
    change energyWeights next = weightUpdate lam (energyWeights cur) (energyWeights old)
    rw [hupdate,diagonal_bb1_reciprocal_mean]
    exact energy_weights_update hcur
  · apply Subtype.ext
    rw [(spectral_map_regular lam _ hR).2]
    rfl

theorem gradient_orbit_state_iterates (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hg : ∀ n, 0 < energy (g n))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1)))
    (n : ℕ) :
    normalizedPair (g (n+1)) (g n) (hg (n+1)) (hg n) =
      (spectralMap lam)^[n] (normalizedPair (g 1) (g 0) (hg 1) (hg 0)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,
      normalized_pair_update (hg n) (hg (n+1)) (hg (n+2)) (hupdate n),ih,
      Function.iterate_succ_apply']

theorem gradient_orbit_norm_step (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hg : ∀ n, 0 < energy (g n))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1)))
    (n : ℕ) :
    normDiag (g (n+2)) =
      stateGrowth lam (normalizedPair (g (n+1)) (g n) (hg (n+1)) (hg n)) * normDiag (g (n+1)) := by
  rw [hupdate n,diagonal_bb1_reciprocal_mean]
  exact norm_update_factorization (hg (n+1))

theorem gradient_orbit_norm_product (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hg : ∀ n, 0 < energy (g n))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1)))
    (n : ℕ) :
    normDiag (g (n+1)) = normDiag (g 1) *
      prefixProduct (stateGrowth lam) (spectralMap lam) n
        (normalizedPair (g 1) (g 0) (hg 1) (hg 0)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show n+1+1=n+2 by omega,gradient_orbit_norm_step lam g hg hupdate n,
      gradient_orbit_state_iterates lam g hg hupdate n,ih]
    rw [prefix_product_cocycle (stateGrowth lam) (spectralMap lam) n 1]
    simp only [prefix_product_succ,prefix_product_zero,mul_one]
    ring

theorem zero_gradient_stays_zero (lam : ι → ℝ) (g : ℕ → ι → ℝ)
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1)))
    (k : ℕ) (hk : g (k+1) = 0) : ∀ n, g (k+1+n) = 0 := by
  intro n
  induction n with
  | zero => simpa using hk
  | succ n ih =>
    have hidx : k+1+(n+1) = (k+n)+2 := by omega
    rw [hidx,hupdate (k+n)]
    have hiz : g (k+n+1) = 0 := by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih
    rw [hiz]
    funext i
    simp [gradientUpdate]

theorem energy_eq_zero_iff (g : ι → ℝ) : energy g = 0 ↔ g = 0 := by
  constructor
  · intro he
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (g i))).mp he
    funext i
    have hi := hall i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  · intro he
    rw [he]
    simp [energy]

end
end BB
