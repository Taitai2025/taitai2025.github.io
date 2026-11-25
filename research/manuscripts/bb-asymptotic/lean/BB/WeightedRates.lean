import BB.ActiveSupport

/-!
# Sharp rates for weighted BB trajectories

The positive diagonal change of coordinates converts the weighted quotient and
update to ordinary BB1. Norm comparisons give the same root factor and transfer
the uniform matched-start estimate back to the original gradient norm.
-/

namespace BB
noncomputable section
open Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma positive_weights_bounds (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ (∀ i, m ≤ ψ i) ∧ (∀ i, ψ i ≤ M) := by
  by_cases hn : Nonempty ι
  · letI : Nonempty ι := hn
    obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ ψ Finset.univ_nonempty
    obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ ψ Finset.univ_nonempty
    exact ⟨ψ lo, ψ hi, hψ lo, hψ hi,
      fun i => hlo i (Finset.mem_univ i), fun i => hhi i (Finset.mem_univ i)⟩
  · letI : IsEmpty ι := not_nonempty_iff.mp hn
    exact ⟨1, 1, zero_lt_one, zero_lt_one, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

lemma spectral_scale_energy_pos (ψ : ι → ℝ) (hψ : ∀ i, 0 < ψ i)
    {g : ι → ℝ} (hg : 0 < energy g) : 0 < energy (spectralScale ψ g) := by
  obtain ⟨m, M, hm, _hM, hlo, _hhi⟩ := positive_weights_bounds ψ hψ
  rw [spectral_scale_energy ψ g (fun i => (hψ i).le)]
  exact (mul_pos hm hg).trans_le (weighted_energy_lower ψ g m hlo)

lemma norm_le_inverse_scale (ψ g : ι → ℝ) (m M : ℝ)
    (hm : 0 < m) (hlo : ∀ i, m ≤ ψ i) (hhi : ∀ i, ψ i ≤ M) :
    normDiag g ≤ (Real.sqrt m)⁻¹ * normDiag (spectralScale ψ g) := by
  have hb := (spectral_scale_norm_bounds ψ g m M hm hlo hhi).1
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hh := mul_le_mul_of_nonneg_left hb (inv_pos.mpr hs).le
  simpa only [← mul_assoc, inv_mul_cancel hs.ne', one_mul] using hh

lemma weighted_gradient_rootTerm_bounded (lam ψ : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hψ : ∀ i, 0 < ψ i) (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => normDiag (g n))) := by
  obtain ⟨m, M, hm, _hM, hlo, hhi⟩ := positive_weights_bounds ψ hψ
  have hb := gradient_rootTerm_bounded lam A B hA hAB hlam
    (fun n => spectralScale ψ (g n)) (spectral_scale_energy_pos ψ hψ hg0)
    (weighted_delayed_update_conjugacy lam ψ g (fun i => (hψ i).le) hupdate)
  apply rootTerm_bounded_of_comparison (fun n => normDiag (g n))
    (fun n => normDiag (spectralScale ψ (g n))) (fun n => norm_diag_nonneg _)
    (fun n => norm_diag_nonneg _) hb (Real.sqrt m)⁻¹ (inv_pos.mpr (Real.sqrt_pos.mpr hm))
  exact Filter.eventually_of_forall fun n => norm_le_inverse_scale ψ (g n) m M hm hlo hhi

/-- Every fixed positive spectral weight has the same sharp upper root factor. -/
lemma weighted_gradient_normalized_rootFactor_le (lam ψ : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hψ : ∀ i, 0 < ψ i) (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ≤ rate A B := by
  have hb := weighted_gradient_rootTerm_bounded lam ψ A B hA hAB hlam hψ g hg0 hupdate
  rw [rootFactor_div_const (fun n => normDiag (g n)) (fun n => norm_diag_nonneg _) hb
    (normDiag (g 0)) (Real.sqrt_pos.mpr hg0)]
  obtain ⟨m, M, hm, hM, hlo, hhi⟩ := positive_weights_bounds ψ hψ
  rw [← weighted_rootFactor_eq ψ g m M hm hM hlo hhi hb]
  exact gradient_rootFactor_le lam A B hA hAB hlam (fun n => spectralScale ψ (g n))
    (spectral_scale_energy_pos ψ hψ hg0)
    (weighted_delayed_update_conjugacy lam ψ g (fun i => (hψ i).le) hupdate)

lemma weighted_matched_first_conjugacy (lam ψ : ι → ℝ) (hψ : ∀ i, 0 ≤ ψ i)
    (g : ℕ → ι → ℝ)
    (hfirst : g 1 = gradientUpdate lam (weightedBB lam ψ (g 0)) (g 0)) :
    spectralScale ψ (g 1) =
      gradientUpdate lam (diagonalBB1 lam (spectralScale ψ (g 0))) (spectralScale ψ (g 0)) := by
  rw [hfirst, spectral_scale_commutes, weighted_quotient_conjugacy lam ψ (g 0) hψ]

lemma weighted_gradient_matched_uniform_envelope (lam ψ : ι → ℝ) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hψ : ∀ i, 0 < ψ i) (hγ : rate A B < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → ι → ℝ), 0 < energy (g 0) →
      g 1 = gradientUpdate lam (weightedBB lam ψ (g 0)) (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) →
      ∀ n, normDiag (g n) ≤ K * γ ^ n * normDiag (g 0) := by
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  obtain ⟨m, M, hm, hM, hlo, hhi⟩ := positive_weights_bounds ψ hψ
  obtain ⟨C, hC, henv⟩ := gradient_matched_uniform_envelope lam A B γ hA hAB hlam hγ
  let K := (Real.sqrt m)⁻¹ * C * Real.sqrt M
  have hsm : 0 < (Real.sqrt m)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hm)
  refine ⟨K, mul_pos (mul_pos hsm hC) (Real.sqrt_pos.mpr hM), ?_⟩
  intro g hg0 hfirst hupdate n
  have he := henv (fun n => spectralScale ψ (g n)) (spectral_scale_energy_pos ψ hψ hg0)
    (weighted_matched_first_conjugacy lam ψ (fun i => (hψ i).le) g hfirst)
    (weighted_delayed_update_conjugacy lam ψ g (fun i => (hψ i).le) hupdate) n
  calc
    normDiag (g n) ≤ (Real.sqrt m)⁻¹ * normDiag (spectralScale ψ (g n)) :=
      norm_le_inverse_scale ψ (g n) m M hm hlo hhi
    _ ≤ (Real.sqrt m)⁻¹ * (C * γ ^ n * normDiag (spectralScale ψ (g 0))) :=
      mul_le_mul_of_nonneg_left he hsm.le
    _ ≤ (Real.sqrt m)⁻¹ * (C * γ ^ n * (Real.sqrt M * normDiag (g 0))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (spectral_scale_norm_bounds ψ (g 0) m M hm hlo hhi).2
          (mul_nonneg hC.le (pow_nonneg hγpos.le n))) hsm.le
    _ = K * γ ^ n * normDiag (g 0) := by dsimp [K]; ring


lemma weighted_orbit_supported (lam ψ : ι → ℝ) (g : ℕ → ι → ℝ) (I : Finset ι)
    (h0 : SupportedOn I (g 0)) (h1 : SupportedOn I (g 1))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) :
    ∀ n, SupportedOn I (g n) := by
  exact Nat.twoStepInduction h0 h1 (fun n _hn hn1 => by
    rw [hupdate n]
    exact gradient_update_supported lam _ hn1)

lemma weighted_bb_congr_on_support {lam mu ψ g : ι → ℝ} {I : Finset ι}
    (hg : SupportedOn I g) (heq : ∀ i ∈ I, lam i = mu i) :
    weightedBB lam ψ g = weightedBB mu ψ g := by
  unfold weightedBB
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · rw [heq i hi]
  · simp only [hg i hi, zero_pow (by decide : 2 ≠ 0), mul_zero]

lemma weighted_orbit_congr_on_support {lam mu ψ : ι → ℝ} (g : ℕ → ι → ℝ) (I : Finset ι)
    (h0 : SupportedOn I (g 0)) (h1 : SupportedOn I (g 1))
    (heq : ∀ i ∈ I, lam i = mu i)
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) :
    ∀ n, g (n + 2) = gradientUpdate mu (weightedBB mu ψ (g n)) (g (n + 1)) := by
  have hsupp := weighted_orbit_supported lam ψ g I h0 h1 hupdate
  intro n
  rw [hupdate n, weighted_bb_congr_on_support (hsupp n) heq]
  exact gradient_update_congr_on_support _ (hsupp (n + 1)) heq

lemma weighted_gradient_supported_rootFactor_le (lam ψ : ι → ℝ) (I : Finset ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i ∈ I, a ≤ lam i ∧ lam i ≤ b)
    (hψ : ∀ i, 0 < ψ i) (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (h0 : SupportedOn I (g 0)) (h1 : SupportedOn I (g 1))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ≤ rate a b := by
  exact weighted_gradient_normalized_rootFactor_le (clippedSpectrum lam I a) ψ a b ha hab
    (clipped_spectrum_bounds lam I a b hab hlam) hψ g hg0
    (weighted_orbit_congr_on_support g I h0 h1 (clipped_spectrum_agrees lam I a) hupdate)

lemma weighted_gradient_active_rootFactor_le (lam ψ : ι → ℝ) (a b α₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hψ : ∀ i, 0 < ψ i)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hlam : ∀ i, g 0 i ≠ 0 → a ≤ lam i ∧ lam i ≤ b)
    (hfirst : g 1 = gradientUpdate lam α₀ (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ≤ rate a b := by
  have h0 := supported_coordinateSupport (g 0)
  have h1 : SupportedOn (coordinateSupport (g 0)) (g 1) := by
    rw [hfirst]
    exact gradient_update_supported lam α₀ h0
  exact weighted_gradient_supported_rootFactor_le lam ψ (coordinateSupport (g 0)) a b ha hab
    (fun i hi => hlam i (Finset.mem_filter.mp hi).2) hψ g hg0 h0 h1 hupdate

lemma weighted_gradient_supported_matched_uniform_envelope (lam ψ : ι → ℝ)
    (I : Finset ι) (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hlam : ∀ i ∈ I, a ≤ lam i ∧ lam i ≤ b) (hψ : ∀ i, 0 < ψ i) (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → ι → ℝ), 0 < energy (g 0) → SupportedOn I (g 0) →
      g 1 = gradientUpdate lam (weightedBB lam ψ (g 0)) (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) →
      ∀ n, normDiag (g n) ≤ K * γ ^ n * normDiag (g 0) := by
  let mu := clippedSpectrum lam I a
  have heq := clipped_spectrum_agrees lam I a
  obtain ⟨K, hK, henv⟩ := weighted_gradient_matched_uniform_envelope mu ψ a b γ ha hab
    (clipped_spectrum_bounds lam I a b hab hlam) hψ hγ
  refine ⟨K, hK, ?_⟩
  intro g hg0 h0 hfirst hupdate
  have h1 : SupportedOn I (g 1) := by
    rw [hfirst]
    exact gradient_update_supported lam _ h0
  have hfirst' : g 1 = gradientUpdate mu (weightedBB mu ψ (g 0)) (g 0) := by
    rw [hfirst, weighted_bb_congr_on_support h0 heq]
    exact gradient_update_congr_on_support _ h0 heq
  exact henv g hg0 hfirst' (weighted_orbit_congr_on_support g I h0 h1 heq hupdate)

end
end BB
