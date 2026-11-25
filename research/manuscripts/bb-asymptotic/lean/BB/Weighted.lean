import BB.Spectral
import BB.Asymptotics

/-! # Fixed positive diagonal weights and BB conjugacy -/

namespace BB
noncomputable section
open scoped BigOperators
open Filter

variable {ι : Type*} [Fintype ι]

def spectralScale (ψ g : ι → ℝ) (i : ι) : ℝ := Real.sqrt (ψ i) * g i
def weightedEnergy (ψ g : ι → ℝ) : ℝ := ∑ i, ψ i * (g i)^2
def weightedBB (lam ψ g : ι → ℝ) : ℝ :=
  weightedEnergy ψ g / ∑ i, ψ i * lam i * (g i)^2
def diagonalBB1 (lam g : ι → ℝ) : ℝ := energy g / ∑ i, lam i * (g i)^2
def normDiag (g : ι → ℝ) : ℝ := Real.sqrt (energy g)

theorem spectral_scale_square (ψ g : ι → ℝ) (hψ : ∀ i, 0 ≤ ψ i) (i : ι) :
    (spectralScale ψ g i)^2 = ψ i * (g i)^2 := by
  unfold spectralScale
  rw [mul_pow, Real.sq_sqrt (hψ i)]

theorem spectral_scale_energy (ψ g : ι → ℝ) (hψ : ∀ i, 0 ≤ ψ i) :
    energy (spectralScale ψ g) = weightedEnergy ψ g := by
  unfold energy weightedEnergy
  exact Finset.sum_congr rfl (fun i _ => spectral_scale_square ψ g hψ i)

theorem spectral_scale_support (ψ g : ι → ℝ) (hψ : ∀ i, 0 < ψ i) (i : ι) :
    spectralScale ψ g i = 0 ↔ g i = 0 := by
  unfold spectralScale
  exact mul_eq_zero.trans (or_iff_right (ne_of_gt (Real.sqrt_pos.2 (hψ i))))

theorem spectral_scale_commutes (lam ψ g : ι → ℝ) (α : ℝ) :
    spectralScale ψ (gradientUpdate lam α g) =
      gradientUpdate lam α (spectralScale ψ g) := by
  funext i
  unfold spectralScale gradientUpdate
  ring

theorem weighted_quotient_conjugacy (lam ψ g : ι → ℝ) (hψ : ∀ i, 0 ≤ ψ i) :
    weightedBB lam ψ g = diagonalBB1 lam (spectralScale ψ g) := by
  unfold weightedBB diagonalBB1
  rw [spectral_scale_energy ψ g hψ]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [spectral_scale_square ψ g hψ i]
  ring

theorem weighted_energy_lower (ψ g : ι → ℝ) (m : ℝ) (hm : ∀ i, m ≤ ψ i) :
    m * energy g ≤ weightedEnergy ψ g := by
  unfold weightedEnergy energy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (sq_nonneg _)

theorem weighted_energy_upper (ψ g : ι → ℝ) (M : ℝ) (hM : ∀ i, ψ i ≤ M) :
    weightedEnergy ψ g ≤ M * energy g := by
  unfold weightedEnergy energy
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM i) (sq_nonneg _)

theorem norm_diag_nonneg (g : ι → ℝ) : 0 ≤ normDiag g := Real.sqrt_nonneg _

theorem norm_diag_pos {g : ι → ℝ} (hg : ∃ i, g i ≠ 0) : 0 < normDiag g :=
  Real.sqrt_pos.2 (energy_pos hg)

theorem spectral_scale_norm_bounds (ψ g : ι → ℝ) (m M : ℝ)
    (hm : 0 < m) (hlo : ∀ i, m ≤ ψ i) (hhi : ∀ i, ψ i ≤ M) :
    Real.sqrt m * normDiag g ≤ normDiag (spectralScale ψ g) ∧
      normDiag (spectralScale ψ g) ≤ Real.sqrt M * normDiag g := by
  have hψ : ∀ i, 0 ≤ ψ i := fun i => (le_of_lt hm).trans (hlo i)
  have hM : 0 ≤ M ∨ energy g = 0 := by
    by_cases hi : Nonempty ι
    · obtain ⟨i⟩ := hi
      exact Or.inl ((hψ i).trans (hhi i))
    · have : IsEmpty ι := not_nonempty_iff.mp hi
      exact Or.inr (by simp [energy])
  unfold normDiag
  rw [spectral_scale_energy ψ g hψ]
  constructor
  · rw [← Real.sqrt_mul (le_of_lt hm)]
    exact Real.sqrt_le_sqrt (weighted_energy_lower ψ g m hlo)
  · rcases hM with hM | he
    · rw [← Real.sqrt_mul hM]
      exact Real.sqrt_le_sqrt (weighted_energy_upper ψ g M hhi)
    · rw [he, Real.sqrt_zero, mul_zero]
      have hupper := weighted_energy_upper ψ g M hhi
      rw [he,mul_zero] at hupper
      exact (Real.sqrt_eq_zero_of_nonpos hupper).le

/-- Actual commutation and quotient identities imply the transformed delayed update. -/
theorem weighted_delayed_update_conjugacy (lam ψ : ι → ℝ) (g : ℕ → ι → ℝ)
    (hψ : ∀ i, 0 ≤ ψ i)
    (hupdate : ∀ k, g (k+2) = gradientUpdate lam (weightedBB lam ψ (g k)) (g (k+1))) :
    ∀ k, spectralScale ψ (g (k+2)) =
      gradientUpdate lam (diagonalBB1 lam (spectralScale ψ (g k)))
        (spectralScale ψ (g (k+1))) := by
  intro k
  rw [hupdate k, spectral_scale_commutes, weighted_quotient_conjugacy lam ψ (g k) hψ]

/-- Norm comparison preserves the real root factor. Root boundedness is explicit;
it follows from any exponential growth envelope, including a bounded-step orbit. -/
theorem weighted_rootFactor_eq (ψ : ι → ℝ) (g : ℕ → ι → ℝ)
    (m M : ℝ) (hm : 0 < m) (hM : 0 < M)
    (hlo : ∀ i, m ≤ ψ i) (hhi : ∀ i, ψ i ≤ M)
    (hbounded : atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => normDiag (g n)))) :
    rootFactor (fun n => normDiag (spectralScale ψ (g n))) =
      rootFactor (fun n => normDiag (g n)) := by
  apply rootFactor_eq_of_comparable
    (fun n => normDiag (spectralScale ψ (g n))) (fun n => normDiag (g n))
    (fun n => norm_diag_nonneg _) (fun n => norm_diag_nonneg _) hbounded
    (Real.sqrt M) ((Real.sqrt m)⁻¹)
    (Real.sqrt_pos.2 hM) (inv_pos.2 (Real.sqrt_pos.2 hm))
  · exact Filter.eventually_of_forall fun n => (spectral_scale_norm_bounds ψ (g n) m M hm hlo hhi).2
  · apply Filter.eventually_of_forall
    intro n
    have hb := (spectral_scale_norm_bounds ψ (g n) m M hm hlo hhi).1
    have hs : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
    have hh := mul_le_mul_of_nonneg_left hb (le_of_lt (inv_pos.2 hs))
    simpa only [← mul_assoc, inv_mul_cancel (ne_of_gt hs), one_mul] using hh

end
end BB
