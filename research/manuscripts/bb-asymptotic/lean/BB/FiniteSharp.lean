import BB.Faces
import BB.SpectralLyapunov
import BB.CompactContraction

/-!
# Sharp finite-dimensional upper bounds by invariant-face induction

This proof applies to the actual delayed spectral map on the whole product of
closed simplexes, including terminal states and repeated spectral values.
Every auxiliary rate is obtained by compactness and induction; no invariant
measure theorem or paper-specific axiom is used.
-/

namespace BB
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_face_uniform_rate (lam : ι → ℝ) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hγ : rate A B < γ) (I : Finset ι) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < γ ∧
      ∀ n (χ : SpectralFace I), facePrefix lam I n χ ≤ C * ρ ^ n := by
  classical
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  have hγpos : 0 < γ := hc0.trans_lt hγ
  refine Finset.strongInductionOn I ?_
  intro I ih
  by_cases hface : Nonempty (SpectralFace I)
  · letI : Nonempty (SpectralFace I) := hface
    let χ0 : SpectralFace I := Classical.choice hface
    have hI : I.Nonempty := support_nonempty χ0.1.1.2 χ0.2.1
    obtain ⟨lo, hloI, hmin⟩ := Finset.exists_min_image I lam hI
    obtain ⟨hi, hhiI, hmax⟩ := Finset.exists_max_image I lam hI
    have hapos : 0 < lam lo := hA.trans_le (hlam lo).1
    have hab : lam lo ≤ lam hi := hmin hi hhiI
    by_cases heq : lam lo = lam hi
    · have hconstant : ∀ i ∈ I, lam i = lam lo := by
        intro i hiI
        exact le_antisymm ((hmax i hiI).trans heq.ge) (hmin i hiI)
      refine ⟨1, zero_lt_one, γ / 2, by linarith, by linarith, ?_⟩
      intro n χ
      cases n with
      | zero => simp [facePrefix]
      | succ n =>
        have hR := constant_face_terminal lam I (lam lo) hapos.ne' hconstant χ
        have hr : stateGrowth lam χ.1 = 0 := by simp [stateGrowth, hR]
        have hp := prefix_product_terminal (stateGrowth lam) (spectralMap lam) χ.1 hr n
        change prefixProduct (stateGrowth lam) (spectralMap lam) (n + 1) χ.1 ≤ 1 * (γ / 2) ^ (n + 1)
        rw [hp]
        positivity
    · have hablt : lam lo < lam hi := lt_of_le_of_ne hab heq
      have hclocal : rate (lam lo) (lam hi) ≤ rate A B :=
        rate_mono_interval hA (hlam lo).1 hab (hlam hi).2
      have hclocalpos := rate_pos hapos hablt
      let V : SpectralFace I → ℝ := fun χ => stateLyapunov (lam lo) (lam hi) lo hi χ.1
      have hV : Continuous V :=
        (state_lyapunov_continuous hapos hablt lo hi).comp continuous_subtype_val
      have hVpos : ∀ χ, 0 ≤ V χ := fun χ => state_lyapunov_nonneg _ _ lo hi χ.1
      have hstep : ∀ χ : SpectralFace I,
          (stateGrowth lam χ.1) ^ 2 * V (faceMap lam I χ) ≤
            rate (lam lo) (lam hi) ^ 2 * V χ := by
        intro χ
        exact state_lyapunov_step_of_mean_bounds hapos hablt rfl rfl χ.1
          ⟨supported_mean_lower χ.1.2.2 χ.2.2 hmin,
            supported_mean_upper χ.1.2.2 χ.2.2 hmax⟩
      have hlyap : ∀ n (χ : SpectralFace I),
          facePrefix lam I n χ ^ 2 * V ((faceMap lam I)^[n] χ) ≤
            (rate (lam lo) (lam hi) ^ 2) ^ n * V χ := by
        intro n χ
        rw [face_prefix_eq_product]
        exact prefix_product_lyapunov (fun χ : SpectralFace I => stateGrowth lam χ.1)
          (faceMap lam I) V (rate (lam lo) (lam hi) ^ 2) (sq_nonneg _) hstep n χ
      have hboundary : ∀ χ : SpectralFace I, V χ = 0 →
          ∃ n : ℕ, 0 < n ∧ facePrefix lam I n χ < γ ^ n := by
        intro χ hVzero
        by_cases hR : 0 < stateGrowthSq lam χ.1
        · let J := positiveSupport χ.1.1.1
          have hzero : χ.1.1.1 lo = 0 ∨ χ.1.1.1 hi = 0 :=
            (state_lyapunov_eq_zero_iff hapos hablt lo hi χ.1).mp hVzero
          have hJI : J ⊂ I := by
            rcases hzero with hlozero | hhizero
            · exact positiveSupport_proper_of_zero χ.2.1 hloI hlozero
            · exact positiveSupport_proper_of_zero χ.2.1 hhiI hhizero
          obtain ⟨C, _hC, ρ, hρ, hργ, henv⟩ := ih J hJI
          let ξ : SpectralFace J :=
            ⟨spectralMap lam χ.1, regular_image_in_current_support lam χ.1 hR⟩
          have htail : ∀ n, prefixProduct (stateGrowth lam) (spectralMap lam) n
              (spectralMap lam χ.1) ≤ C * ρ ^ n := fun n => henv n ξ
          exact strict_prefix_of_tail_envelope (stateGrowth lam) (spectralMap lam) χ.1
            (state_growth_nonneg lam χ.1) C ρ γ hρ.le hγpos hργ htail
        · have hRzero : stateGrowthSq lam χ.1 = 0 :=
            le_antisymm (le_of_not_gt hR) (growth_sq_nonneg χ.1.1.2)
          have hr : stateGrowth lam χ.1 = 0 := by simp [stateGrowth, hRzero]
          refine ⟨1, by omega, ?_⟩
          change prefixProduct (stateGrowth lam) (spectralMap lam) 1 χ.1 < γ ^ 1
          simpa only [prefix_product_succ, prefix_product_zero, hr, zero_mul, pow_one] using hγpos
      exact compact_boundary_lyapunov_improved_rate (faceMap lam I) (facePrefix lam I)
        (fun χ => rfl) (face_prefix_continuous lam A B hA hAB hlam I)
        (fun n χ => prefix_product_nonneg (stateGrowth lam) (spectralMap lam)
          (state_growth_nonneg lam) n χ.1)
        (face_prefix_cocycle lam I) V hV hVpos (rate (lam lo) (lam hi) ^ 2) γ
        (sq_nonneg _) hγpos (by nlinarith) hlyap hboundary
  · refine ⟨1, zero_lt_one, γ / 2, by linarith, by linarith, ?_⟩
    intro n χ
    exact (hface ⟨χ⟩).elim

lemma finite_spectral_uniform_rate (lam : ι → ℝ) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hγ : rate A B < γ) :
    ∃ C : ℝ, 0 < C ∧ ∃ ρ : ℝ, 0 < ρ ∧ ρ < γ ∧
      ∀ n (χ : SpectralState ι),
        prefixProduct (stateGrowth lam) (spectralMap lam) n χ ≤ C * ρ ^ n := by
  obtain ⟨C, hC, ρ, hρ, hργ, henv⟩ := finite_face_uniform_rate lam A B γ hA hAB hlam hγ Finset.univ
  refine ⟨C, hC, ρ, hρ, hργ, ?_⟩
  intro n χ
  have hχ : InFace Finset.univ χ := by
    constructor <;> intro i hi <;> exact (hi (Finset.mem_univ i)).elim
  exact henv n ⟨χ, hχ⟩

lemma finite_spectral_envelope (lam : ι → ℝ) (A B γ : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (hγ : rate A B < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n (χ : SpectralState ι),
      prefixProduct (stateGrowth lam) (spectralMap lam) n χ ≤ C * γ ^ n := by
  obtain ⟨C, hC, ρ, hρ, hργ, henv⟩ := finite_spectral_uniform_rate lam A B γ hA hAB hlam hγ
  refine ⟨C, hC, ?_⟩
  intro n χ
  exact (henv n χ).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left hρ.le hργ.le n) hC.le)

lemma finite_spectral_rootFactor_le (lam : ι → ℝ) (A B : ℝ)
    (hA : 0 < A) (hAB : A ≤ B) (hlam : ∀ i, A ≤ lam i ∧ lam i ≤ B)
    (χ : SpectralState ι) :
    rootFactor (fun n => prefixProduct (stateGrowth lam) (spectralMap lam) n χ) ≤ rate A B := by
  apply le_of_forall_strict_upper_bound
  intro γ hγ
  obtain ⟨C, hC, henv⟩ := finite_spectral_envelope lam A B γ hA hAB hlam hγ
  have hc0 : 0 ≤ rate A B := by
    unfold rate
    exact div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  apply rootFactor_le_of_envelope _
    (fun n => prefix_product_nonneg (stateGrowth lam) (spectralMap lam) (state_growth_nonneg lam) n χ)
    γ (hc0.trans hγ.le)
  exact ⟨C, hC, fun n => henv n χ⟩

end
end BB
