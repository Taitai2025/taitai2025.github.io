import BB.GradientRates

/-!
# Active spectral support

Changing eigenvalues outside the initial gradient's coordinate support leaves
the trajectory unchanged. This gives the sharp bound on the active spectral
interval without assumptions on inactive coordinates.
-/

namespace BB
noncomputable section
open Filter
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateSupport (g : ι → ℝ) : Finset ι :=
  Finset.univ.filter (fun i => g i ≠ 0)

lemma supported_coordinateSupport (g : ι → ℝ) : SupportedOn (coordinateSupport g) g := by
  intro i hi
  by_contra hne
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hne⟩)

lemma gradient_update_supported (lam : ι → ℝ) (α : ℝ) {I : Finset ι} {g : ι → ℝ}
    (hg : SupportedOn I g) : SupportedOn I (gradientUpdate lam α g) := by
  intro i hi
  simp only [gradientUpdate, hg i hi, mul_zero]

lemma gradient_orbit_supported (lam : ι → ℝ) (g : ℕ → ι → ℝ) (I : Finset ι)
    (h0 : SupportedOn I (g 0)) (h1 : SupportedOn I (g 1))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    ∀ n, SupportedOn I (g n) := by
  exact Nat.twoStepInduction h0 h1 (fun n _hn hn1 => by
    rw [hupdate n]
    exact gradient_update_supported lam _ hn1)

lemma diagonal_bb1_congr_on_support {lam mu g : ι → ℝ} {I : Finset ι}
    (hg : SupportedOn I g) (heq : ∀ i ∈ I, lam i = mu i) :
    diagonalBB1 lam g = diagonalBB1 mu g := by
  unfold diagonalBB1
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I
  · rw [heq i hi]
  · simp only [hg i hi, zero_pow (by decide : 2 ≠ 0), mul_zero]

lemma gradient_update_congr_on_support {lam mu g : ι → ℝ} {I : Finset ι} (α : ℝ)
    (hg : SupportedOn I g) (heq : ∀ i ∈ I, lam i = mu i) :
    gradientUpdate lam α g = gradientUpdate mu α g := by
  funext i
  by_cases hi : i ∈ I
  · simp only [gradientUpdate, heq i hi]
  · simp only [gradientUpdate, hg i hi, mul_zero]

/-- Arbitrary values may be placed on coordinates outside the invariant support. -/
lemma gradient_orbit_congr_on_support {lam mu : ι → ℝ} (g : ℕ → ι → ℝ) (I : Finset ι)
    (h0 : SupportedOn I (g 0)) (h1 : SupportedOn I (g 1))
    (heq : ∀ i ∈ I, lam i = mu i)
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    ∀ n, g (n + 2) = gradientUpdate mu (diagonalBB1 mu (g n)) (g (n + 1)) := by
  have hsupp := gradient_orbit_supported lam g I h0 h1 hupdate
  intro n
  rw [hupdate n, diagonal_bb1_congr_on_support (hsupp n) heq]
  exact gradient_update_congr_on_support _ (hsupp (n + 1)) heq

def clippedSpectrum (lam : ι → ℝ) (I : Finset ι) (a : ℝ) (i : ι) : ℝ :=
  if i ∈ I then lam i else a

lemma clipped_spectrum_agrees (lam : ι → ℝ) (I : Finset ι) (a : ℝ) :
    ∀ i ∈ I, lam i = clippedSpectrum lam I a i := by
  intro i hi
  simp [clippedSpectrum, hi]

lemma clipped_spectrum_bounds (lam : ι → ℝ) (I : Finset ι) (a b : ℝ)
    (hab : a ≤ b) (hlam : ∀ i ∈ I, a ≤ lam i ∧ lam i ≤ b) :
    ∀ i, a ≤ clippedSpectrum lam I a i ∧ clippedSpectrum lam I a i ≤ b := by
  intro i
  by_cases hi : i ∈ I
  · simpa [clippedSpectrum, hi] using hlam i hi
  · simp [clippedSpectrum, hi, hab]

lemma gradient_supported_rootFactor_le (lam : ι → ℝ) (I : Finset ι) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i ∈ I, a ≤ lam i ∧ lam i ≤ b)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (h0 : SupportedOn I (g 0)) (h1 : SupportedOn I (g 1))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ≤ rate a b := by
  exact gradient_normalized_rootFactor_le (clippedSpectrum lam I a) a b ha hab
    (clipped_spectrum_bounds lam I a b hab hlam) g hg0
    (gradient_orbit_congr_on_support g I h0 h1 (clipped_spectrum_agrees lam I a) hupdate)

/-- Active-hull bound for an arbitrary first scalar gradient step. -/
lemma gradient_active_rootFactor_le (lam : ι → ℝ) (a b α₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b)
    (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hlam : ∀ i, g 0 i ≠ 0 → a ≤ lam i ∧ lam i ≤ b)
    (hfirst : g 1 = gradientUpdate lam α₀ (g 0))
    (hupdate : ∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) :
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) ≤ rate a b := by
  have h0 := supported_coordinateSupport (g 0)
  have h1 : SupportedOn (coordinateSupport (g 0)) (g 1) := by
    rw [hfirst]
    exact gradient_update_supported lam α₀ h0
  exact gradient_supported_rootFactor_le lam (coordinateSupport (g 0)) a b ha hab
    (fun i hi => hlam i (Finset.mem_filter.mp hi).2) g hg0 h0 h1 hupdate

/-- A common exponential constant for all matched trajectories supported on a
fixed active face, independent of their amplitudes. -/
lemma gradient_supported_matched_uniform_envelope (lam : ι → ℝ) (I : Finset ι) (a b γ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i ∈ I, a ≤ lam i ∧ lam i ≤ b)
    (hγ : rate a b < γ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : ℕ → ι → ℝ), 0 < energy (g 0) → SupportedOn I (g 0) →
      g 1 = gradientUpdate lam (diagonalBB1 lam (g 0)) (g 0) →
      (∀ n, g (n + 2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n + 1))) →
      ∀ n, normDiag (g n) ≤ K * γ ^ n * normDiag (g 0) := by
  let mu := clippedSpectrum lam I a
  have heq := clipped_spectrum_agrees lam I a
  obtain ⟨K, hK, henv⟩ := gradient_matched_uniform_envelope mu a b γ ha hab
    (clipped_spectrum_bounds lam I a b hab hlam) hγ
  refine ⟨K, hK, ?_⟩
  intro g hg0 h0 hfirst hupdate
  have h1 : SupportedOn I (g 1) := by
    rw [hfirst]
    exact gradient_update_supported lam _ h0
  have hfirst' : g 1 = gradientUpdate mu (diagonalBB1 mu (g 0)) (g 0) := by
    rw [hfirst, diagonal_bb1_congr_on_support h0 heq]
    exact gradient_update_congr_on_support _ h0 heq
  exact henv g hg0 hfirst' (gradient_orbit_congr_on_support g I h0 h1 heq hupdate)

end
end BB
