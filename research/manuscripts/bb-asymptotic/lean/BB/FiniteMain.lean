import BB.EndpointSpectrum
import BB.WeightedRates

/-!
# Finite-dimensional main theorems: attained suprema and infima of uniform rates

The admissible sets below quantify over actual delayed gradient trajectories,
nonzero initial gradients, and positive first scalar steps. Matched uniform
rates quantify over all initial gradients with one common exponential constant.
-/

namespace BB
noncomputable section
open Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma weighted_bb_one (lam g : ι → ℝ) : weightedBB lam (fun _ => 1) g = diagonalBB1 lam g := by
  simp [weightedBB, weightedEnergy, diagonalBB1, energy]

lemma diagonal_bb1_pos (lam : ι → ℝ) (a : ℝ) (ha : 0 < a) (hlam : ∀ i, a ≤ lam i)
    {g : ι → ℝ} (hg : 0 < energy g) : 0 < diagonalBB1 lam g := by
  apply div_pos hg
  exact (mul_pos ha hg).trans_le (weighted_energy_lower lam g a hlam)

lemma weighted_bb_pos (lam ψ : ι → ℝ) (a : ℝ) (ha : 0 < a) (hlam : ∀ i, a ≤ lam i)
    (hψ : ∀ i, 0 < ψ i) {g : ι → ℝ} (hg : 0 < energy g) : 0 < weightedBB lam ψ g := by
  rw [weighted_quotient_conjugacy lam ψ g (fun i => (hψ i).le)]
  exact diagonal_bb1_pos lam a ha hlam (spectral_scale_energy_pos ψ hψ hg)

lemma spectral_scale_endpoint_gradient (lam ψ : ι → ℝ) (lo hi : ι) (x y : ℝ) (n : ℕ) :
    spectralScale ψ (endpointGradient lam lo hi x y n) =
      endpointGradient lam lo hi (Real.sqrt (ψ lo) * x) (Real.sqrt (ψ hi) * y) n := by
  funext i
  by_cases hlo : i = lo
  · subst i
    simp only [spectralScale, endpointGradient, pairEmbed, if_true]
    ring
  · by_cases hhi : i = hi
    · subst i
      simp only [spectralScale, endpointGradient, pairEmbed, hlo, if_false, if_true]
      ring
    · simp only [spectralScale, endpointGradient, pairEmbed, hlo, hhi, if_false, mul_zero]

lemma weighted_endpoint_sharp (lam ψ : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (ha : 0 < lam lo) (hab : lam lo < lam hi) (hψ : ∀ i, 0 < ψ i) :
    ∃ g : ℕ → ι → ℝ, 0 < energy (g 0) ∧ 0 < weightedBB lam ψ (g 0) ∧
      g 1 = gradientUpdate lam (weightedBB lam ψ (g 0)) (g 0) ∧
      (∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) ∧
      (∀ n, normDiag (g n) = (rate (lam lo) (lam hi))^n * normDiag (g 0)) ∧
      rootFactor (fun n => normDiag (g n) / normDiag (g 0)) = rate (lam lo) (lam hi) := by
  let x := (Real.sqrt (ψ lo))⁻¹
  let y := (Real.sqrt (ψ hi))⁻¹
  let g := endpointGradient lam lo hi x y
  have hx : 0 < x := inv_pos.mpr (Real.sqrt_pos.mpr (hψ lo))
  have hscale : ∀ n, spectralScale ψ (g n) = endpointGradient lam lo hi 1 1 n := by
    intro n
    rw [spectral_scale_endpoint_gradient]
    dsimp [x, y]
    rw [mul_inv_cancel (Real.sqrt_pos.mpr (hψ lo)).ne', mul_inv_cancel (Real.sqrt_pos.mpr (hψ hi)).ne']
  have hq : ∀ n, weightedBB lam ψ (g n) = 2 / (lam lo + lam hi) := by
    intro n
    rw [weighted_quotient_conjugacy lam ψ (g n) (fun i => (hψ i).le), hscale n]
    exact endpoint_gradient_quotient lam lo hi hne 1 1 ha hab one_ne_zero rfl n
  have hg0 : 0 < energy (g 0) := by
    simp only [g, endpointGradient, pow_zero, one_mul, pair_embed_energy lo hi hne]
    nlinarith [sq_pos_of_pos hx, sq_nonneg y]
  have hnorm : ∀ n, normDiag (g n) = (rate (lam lo) (lam hi))^n * normDiag (g 0) :=
    endpoint_gradient_norm lam lo hi hne x y ha hab
  refine ⟨g, hg0, ?_, ?_, ?_, hnorm, ?_⟩
  · rw [hq 0]
    exact div_pos (by norm_num) (by linarith)
  · rw [hq 0]
    exact (endpoint_gradient_step lam lo hi x y ha hab 0).symm
  · intro n
    rw [hq n]
    exact (endpoint_gradient_step lam lo hi x y ha hab (n + 1)).symm
  · have hn0 : normDiag (g 0) ≠ 0 := (Real.sqrt_pos.mpr hg0).ne'
    have heq : (fun n => normDiag (g n) / normDiag (g 0)) =
        (fun n => (1 : ℝ) * (rate (lam lo) (lam hi))^n) := by
      funext n
      rw [hnorm n, mul_div_cancel_right₀ _ hn0, one_mul]
    rw [heq]
    exact rootFactor_geometric 1 _ zero_lt_one (rate_pos ha hab).le

def singleModeTrajectory (i : ι) (n : ℕ) (j : ι) : ℝ :=
  if n = 0 then if j = i then 1 else 0 else 0

lemma single_mode_initial_energy (i : ι) : energy (singleModeTrajectory i 0) = 1 := by
  simp [energy, singleModeTrajectory]

lemma single_mode_weighted_quotient (lam ψ : ι → ℝ) (i : ι) (hψ : 0 < ψ i) :
    weightedBB lam ψ (singleModeTrajectory i 0) = 1 / lam i := by
  simp only [weightedBB, weightedEnergy, singleModeTrajectory, if_true]
  simp only [ite_pow, one_pow, zero_pow (by decide : 2 ≠ 0), mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [div_mul_eq_div_div, div_self hψ.ne']

lemma single_mode_weighted_sharp (lam ψ : ι → ℝ) (i : ι) (hi : 0 < lam i) (hψ : 0 < ψ i) :
    let g := singleModeTrajectory i
    0 < energy (g 0) ∧ 0 < weightedBB lam ψ (g 0) ∧
      g 1 = gradientUpdate lam (weightedBB lam ψ (g 0)) (g 0) ∧
      (∀ n, g (n + 2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n + 1))) ∧
      rootFactor (fun n => normDiag (g n) / normDiag (g 0)) = 0 := by
  dsimp only
  refine ⟨by rw [single_mode_initial_energy]; norm_num, ?_, ?_, ?_, ?_⟩
  · rw [single_mode_weighted_quotient lam ψ i hψ]
    exact one_div_pos.mpr hi
  · rw [single_mode_weighted_quotient lam ψ i hψ]
    funext j
    by_cases hj : j = i
    · subst j
      simp [gradientUpdate, singleModeTrajectory, hi.ne']
    · simp [gradientUpdate, singleModeTrajectory, hj]
  · intro n
    funext j
    simp [gradientUpdate, singleModeTrajectory]
  · apply rootFactor_eq_zero_of_eventually_zero
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := by omega
    simp [singleModeTrajectory, hn0, normDiag, energy]


/-- The actual delayed gradient recurrence with a positive arbitrary first step. -/
structure IsDelayedTrajectory (lam : ι → ℝ) (step : (ι → ℝ) → ℝ)
    (g : ℕ → ι → ℝ) (α₀ : ℝ) : Prop where
  initial_pos : 0 < energy (g 0)
  firstStep_pos : 0 < α₀
  first : g 1 = gradientUpdate lam α₀ (g 0)
  update : ∀ n, g (n + 2) = gradientUpdate lam (step (g n)) (g (n + 1))

def normalizedTrajectoryFactor (g : ℕ → ι → ℝ) : ℝ :=
  rootFactor (fun n => normDiag (g n) / normDiag (g 0))

def attainableFactors (lam : ι → ℝ) (step : (ι → ℝ) → ℝ) : Set ℝ :=
  {ρ | ∃ (g : ℕ → ι → ℝ) (α₀ : ℝ), IsDelayedTrajectory lam step g α₀ ∧
    normalizedTrajectoryFactor g = ρ}

def matchedUniformRates (lam : ι → ℝ) (step : (ι → ℝ) → ℝ) : Set ℝ :=
  {γ | 0 < γ ∧ γ < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ → ι → ℝ),
    IsDelayedTrajectory lam step g (step (g 0)) →
      ∀ n, normDiag (g n) ≤ C * γ^n * normDiag (g 0)}

/-- Both the distinct-endpoint and singleton-spectrum cases have an actual
matched trajectory attaining the sharp factor. -/
lemma weighted_matched_factor_attained (lam ψ : ι → ℝ) (lo hi : ι)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hψ : ∀ i, 0 < ψ i) :
    ∃ g : ℕ → ι → ℝ, IsDelayedTrajectory lam (weightedBB lam ψ) g (weightedBB lam ψ (g 0)) ∧
      normalizedTrajectoryFactor g = rate a b := by
  rcases lt_or_eq_of_le hab with hablt | rfl
  · have hne : lo ≠ hi := by intro he; have hh := congrArg lam he; rw [hlo, hhi] at hh; linarith
    obtain ⟨g, hg0, hα, hfirst, hupdate, _hnorm, hroot⟩ := weighted_endpoint_sharp lam ψ lo hi hne
      (hlo ▸ ha) (by simpa only [hlo, hhi] using hablt) hψ
    refine ⟨g, ⟨hg0, hα, hfirst, hupdate⟩, ?_⟩
    simpa only [normalizedTrajectoryFactor, hlo, hhi] using hroot
  · obtain ⟨hg0, hα, hfirst, hupdate, hroot⟩ := single_mode_weighted_sharp lam ψ lo (hlo ▸ ha) (hψ lo)
    refine ⟨singleModeTrajectory lo, ⟨hg0, hα, hfirst, hupdate⟩, ?_⟩
    simpa only [normalizedTrajectoryFactor, rate, sub_self, zero_div] using hroot

lemma matched_rate_lower_of_attainment (lam : ι → ℝ) (step : (ι → ℝ) → ℝ) (c γ : ℝ)
    (hattain : ∃ g, IsDelayedTrajectory lam step g (step (g 0)) ∧ normalizedTrajectoryFactor g = c)
    (hγ : γ ∈ matchedUniformRates lam step) : c ≤ γ := by
  obtain ⟨g, hg, hroot⟩ := hattain
  obtain ⟨hγ0, _hγ1, C, hC, henv⟩ := hγ
  have hn0 : 0 < normDiag (g 0) := Real.sqrt_pos.mpr hg.initial_pos
  rw [← hroot]
  apply rootFactor_le_of_envelope (fun n => normDiag (g n) / normDiag (g 0))
    (fun n => div_nonneg (norm_diag_nonneg _) hn0.le) γ hγ0.le
  refine ⟨C, hC, ?_⟩
  intro n
  exact (div_le_iff hn0).mpr (henv g hg n)

lemma isGLB_of_rate_interval (s : Set ℝ) (c : ℝ) (hc : c < 1)
    (hlo : ∀ γ ∈ s, c ≤ γ) (hhi : ∀ γ, c < γ → γ < 1 → γ ∈ s) : IsGLB s c := by
  refine ⟨hlo, ?_⟩
  intro d hd
  apply le_of_forall_strict_upper_bound
  intro z hz
  by_cases hz1 : z < 1
  · exact hd (hhi z hz hz1)
  · have hcm : c < (c + 1) / 2 := by linarith
    have hm1 : (c + 1) / 2 < 1 := by linarith
    have hdm := hd (hhi ((c + 1) / 2) hcm hm1)
    linarith

/-- The weighted finite-dimensional sharp worst-case factor is an attained maximum. -/
lemma finite_weighted_isGreatest (lam ψ : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    IsGreatest (attainableFactors lam (weightedBB lam ψ)) (rate a b) := by
  obtain ⟨g, hg, hroot⟩ := weighted_matched_factor_attained lam ψ lo hi a b ha hab hlo hhi hψ
  refine ⟨⟨g, weightedBB lam ψ (g 0), hg, hroot⟩, ?_⟩
  rintro r ⟨v, α₀, hv, rfl⟩
  exact weighted_gradient_normalized_rootFactor_le lam ψ a b ha hab hlam hψ v hv.initial_pos hv.update

lemma finite_weighted_supremum (lam ψ : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    sSup (attainableFactors lam (weightedBB lam ψ)) = rate a b :=
  (finite_weighted_isGreatest lam ψ lo hi a b ha hab hlo hhi hlam hψ).csSup_eq

lemma finite_weighted_uniform_rate_mem (lam ψ : ι → ℝ) (a b γ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hψ : ∀ i, 0 < ψ i) (hγ : rate a b < γ) (hγ1 : γ < 1) :
    γ ∈ matchedUniformRates lam (weightedBB lam ψ) := by
  have hc0 : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  obtain ⟨C, hC, henv⟩ := weighted_gradient_matched_uniform_envelope lam ψ a b γ ha hab hlam hψ hγ
  exact ⟨hc0.trans_lt hγ, hγ1, C, hC, fun g hg => henv g hg.initial_pos hg.first hg.update⟩

lemma finite_weighted_uniform_isGLB (lam ψ : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    IsGLB (matchedUniformRates lam (weightedBB lam ψ)) (rate a b) := by
  apply isGLB_of_rate_interval _ _ (rate_lt_one ha hab)
  · intro γ hγ
    exact matched_rate_lower_of_attainment lam (weightedBB lam ψ) (rate a b) γ
      (weighted_matched_factor_attained lam ψ lo hi a b ha hab hlo hhi hψ) hγ
  · intro γ hγ hγ1
    exact finite_weighted_uniform_rate_mem lam ψ a b γ ha hab hlam hψ hγ hγ1

lemma finite_weighted_uniform_rate_infimum (lam ψ : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    sInf (matchedUniformRates lam (weightedBB lam ψ)) = rate a b := by
  apply (finite_weighted_uniform_isGLB lam ψ lo hi a b ha hab hlo hhi hlam hψ).csInf_eq
  refine ⟨(rate a b + 1) / 2, ?_⟩
  have hc := rate_lt_one ha hab
  exact finite_weighted_uniform_rate_mem lam ψ a b _ ha hab hlam hψ (by linarith) (by linarith)

lemma finite_bb1_isGreatest (lam : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    IsGreatest (attainableFactors lam (diagonalBB1 lam)) (rate a b) := by
  have hq : weightedBB lam (fun _ => 1) = diagonalBB1 lam := funext (weighted_bb_one lam)
  simpa only [hq] using finite_weighted_isGreatest lam (fun _ => 1) lo hi a b
    ha hab hlo hhi hlam (fun _ => zero_lt_one)

lemma finite_bb1_supremum (lam : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    sSup (attainableFactors lam (diagonalBB1 lam)) = rate a b :=
  (finite_bb1_isGreatest lam lo hi a b ha hab hlo hhi hlam).csSup_eq

lemma finite_bb1_uniform_rate_infimum (lam : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b) :
    sInf (matchedUniformRates lam (diagonalBB1 lam)) = rate a b := by
  have hq : weightedBB lam (fun _ => 1) = diagonalBB1 lam := funext (weighted_bb_one lam)
  simpa only [hq] using finite_weighted_uniform_rate_infimum lam (fun _ => 1) lo hi a b
    ha hab hlo hhi hlam (fun _ => zero_lt_one)

lemma finite_extreme_indices [Nonempty ι] (lam : ι → ℝ) :
    ∃ lo hi : ι, ∀ i, lam lo ≤ lam i ∧ lam i ≤ lam hi := by
  obtain ⟨lo, _, hlo⟩ := Finset.exists_min_image Finset.univ lam Finset.univ_nonempty
  obtain ⟨hi, _, hhi⟩ := Finset.exists_max_image Finset.univ lam Finset.univ_nonempty
  exact ⟨lo, hi, fun i => ⟨hlo i (Finset.mem_univ i), hhi i (Finset.mem_univ i)⟩⟩

/-- Canonical finite weighted main theorem, deriving the extreme indices from
the nonempty positive spectrum. It includes the singleton case automatically. -/
lemma finite_weighted_main [Nonempty ι] (lam ψ : ι → ℝ)
    (hlam : ∀ i, 0 < lam i) (hψ : ∀ i, 0 < ψ i) :
    ∃ lo hi : ι, (∀ i, lam lo ≤ lam i ∧ lam i ≤ lam hi) ∧
      sSup (attainableFactors lam (weightedBB lam ψ)) = rate (lam lo) (lam hi) ∧
      sInf (matchedUniformRates lam (weightedBB lam ψ)) = rate (lam lo) (lam hi) := by
  obtain ⟨lo, hi, hbounds⟩ := finite_extreme_indices lam
  exact ⟨lo, hi, hbounds,
    finite_weighted_supremum lam ψ lo hi (lam lo) (lam hi) (hlam lo) (hbounds hi).1 rfl rfl hbounds hψ,
    finite_weighted_uniform_rate_infimum lam ψ lo hi (lam lo) (lam hi)
      (hlam lo) (hbounds hi).1 rfl rfl hbounds hψ⟩

lemma finite_bb1_main [Nonempty ι] (lam : ι → ℝ) (hlam : ∀ i, 0 < lam i) :
    ∃ lo hi : ι, (∀ i, lam lo ≤ lam i ∧ lam i ≤ lam hi) ∧
      sSup (attainableFactors lam (diagonalBB1 lam)) = rate (lam lo) (lam hi) ∧
      sInf (matchedUniformRates lam (diagonalBB1 lam)) = rate (lam lo) (lam hi) := by
  have hq : weightedBB lam (fun _ => 1) = diagonalBB1 lam := funext (weighted_bb_one lam)
  simpa only [hq] using finite_weighted_main lam (fun _ => 1) hlam (fun _ => zero_lt_one)

end
end BB
