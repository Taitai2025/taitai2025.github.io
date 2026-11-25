import BB.FiniteOperatorMain
import BB.HilbertApproxOrbit
import BB.HilbertApproxBB2

/-!
# Exact Hilbert uniform thresholds with the manuscript's admissible interval

The sets here quantify over every actual matched trajectory and impose
`0 < γ < 1`, exactly as in the source definition. Both scalar and nonscalar
operators are included, and the endpoints are actual real spectrum members.
-/

namespace BB
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem operator_spectrum_subset_form_interval [CompleteSpace E] (A : E →L[ℝ] E)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) : spectrum ℝ A ⊆ Set.Icc a b := by
  intro ell hell
  constructor
  · by_contra hn
    have _hlt : ell < a := lt_of_not_ge hn
    obtain ⟨x,hx,hRay⟩ := spectrum_lower_rayleigh A ell ((a-ell)/2) hell (by linarith)
    have hb := (hbounds x).1
    rw [hx,one_pow,mul_one] at hb
    linarith
  · by_contra hn
    have _hlt : b < ell := lt_of_not_ge hn
    obtain ⟨x,hx,hRay⟩ := spectrum_upper_rayleigh A ell ((ell-b)/2) hell (by linarith)
    have hb := (hbounds x).2
    rw [hx,one_pow,mul_one] at hb
    linarith

theorem operator_form_endpoints_are_spectral_extremes [CompleteSpace E] (A : E →L[ℝ] E)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (ha : a ∈ spectrum ℝ A) (hb : b ∈ spectrum ℝ A) :
    IsLeast (spectrum ℝ A) a ∧ IsGreatest (spectrum ℝ A) b := by
  have hs := operator_spectrum_subset_form_interval A a b hbounds
  exact ⟨⟨ha,fun _ h => (hs h).1⟩,⟨hb,fun _ h => (hs h).2⟩⟩

theorem hilbert_operator_uniform_rate_mem (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (hγ : rate a b < γ) (hγ1 : γ < 1) :
    γ ∈ operatorMatchedUniformRates A.toLinearMap (operatorBB1 A.toLinearMap) := by
  obtain ⟨C,hC,henv⟩ := hilbert_matched_uniform_envelope A hA a b γ ha hab hbounds hγ
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  exact ⟨hc.trans_lt hγ,hγ1,C,hC,fun g hg => henv g hg.initial_ne hg.first hg.update⟩

theorem hilbert_operator_uniform_isGLB [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    IsGLB (operatorMatchedUniformRates A.toLinearMap (operatorBB1 A.toLinearMap)) (rate a b) := by
  apply isGLB_of_rate_interval _ _ (rate_lt_one ha hab)
  · intro γ hγ
    obtain ⟨hγ0,_hγ1,C,hC,henv⟩ := hγ
    rcases hab.lt_or_eq with hablt | rfl
    · apply hilbert_spectral_uniform_rate_ge A hA a b ha hablt hbounds haspec hbspec C γ hC hγ0.le
      intro x hx k
      exact henv (matchedOperatorOrbit A x)
        ⟨hx,(positive_operator_bb1_bounds A a b ha (ha.trans_le hab) hbounds x hx).1,
          matchedOperatorOrbit_one A x,matchedOperatorOrbit_update A x⟩ k
    · simpa only [rate,sub_self,zero_div] using hγ0.le
  · intro γ hγ hγ1
    exact hilbert_operator_uniform_rate_mem A hA a b γ ha hab hbounds hγ hγ1

theorem hilbert_operator_uniform_infimum [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    sInf (operatorMatchedUniformRates A.toLinearMap (operatorBB1 A.toLinearMap)) = rate a b := by
  apply (hilbert_operator_uniform_isGLB A hA a b ha hab hbounds haspec hbspec).csInf_eq
  have hc := rate_lt_one ha hab
  exact ⟨(rate a b+1)/2,hilbert_operator_uniform_rate_mem A hA a b _ ha hab hbounds
    (by linarith) (by linarith)⟩

theorem hilbert_operator_bb2_uniform_rate_mem (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b γ : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2) (hγ : rate a b < γ) (hγ1 : γ < 1) :
    γ ∈ operatorMatchedUniformRates A.toLinearMap (operatorBB2 A.toLinearMap) := by
  obtain ⟨C,hC,henv⟩ := bb2_matched_uniform_family_envelope a b γ ha hab hγ
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  exact ⟨hc.trans_lt hγ,hγ1,C,hC,fun g hg => henv E A hA hbounds g hg.initial_ne hg.first hg.update⟩

theorem hilbert_operator_bb2_uniform_isGLB [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    IsGLB (operatorMatchedUniformRates A.toLinearMap (operatorBB2 A.toLinearMap)) (rate a b) := by
  apply isGLB_of_rate_interval _ _ (rate_lt_one ha hab)
  · intro γ hγ
    obtain ⟨hγ0,_hγ1,C,hC,henv⟩ := hγ
    rcases hab.lt_or_eq with hablt | rfl
    · apply hilbert_bb2_spectral_uniform_rate_ge A hA a b ha hablt hbounds haspec hbspec C γ hC hγ0.le
      intro x hx k
      exact henv (matchedBB2Orbit A x)
        ⟨hx,(positive_operator_bb2_pos_and_upper A hA a b ha hab hbounds x hx).1,
          matchedBB2Orbit_one A x,matchedBB2Orbit_update A x⟩ k
    · simpa only [rate,sub_self,zero_div] using hγ0.le
  · intro γ hγ hγ1
    exact hilbert_operator_bb2_uniform_rate_mem A hA a b γ ha hab hbounds hγ hγ1

theorem hilbert_operator_bb2_uniform_infimum [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    sInf (operatorMatchedUniformRates A.toLinearMap (operatorBB2 A.toLinearMap)) = rate a b := by
  apply (hilbert_operator_bb2_uniform_isGLB A hA a b ha hab hbounds haspec hbspec).csInf_eq
  have hc := rate_lt_one ha hab
  exact ⟨(rate a b+1)/2,hilbert_operator_bb2_uniform_rate_mem A hA a b _ ha hab hbounds
    (by linarith) (by linarith)⟩

end
end BB
