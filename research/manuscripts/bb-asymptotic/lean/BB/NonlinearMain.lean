import BB.NonlinearUniversal
import BB.NonlinearObjective
import BB.NonlinearTranslation

/-!
# The complete local nonlinear BB convergence theorem

This module discharges both the positive-operator model and the quadratic
uniform-envelope inputs.  The theorem uses an arbitrary stationary point and
the actual untranslated BB orbit, for either fixed classical rule.
-/

noncomputable section
namespace BB.Nonlinear

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The uniform local conclusions, using the paper's initial-pair radius and
the actual algorithm.  The three positive constants are independent of the pair. -/
def LocalGuarantee (rule : Rule) (F : E → ℝ) (G : E → E) (a : E) (c γ R : ℝ) : Prop :=
  ∃ r > 0, r ≤ R ∧ ∃ ρ > 0, ρ ≤ r ∧ ∃ Ce > 0, ∃ Cg > 0, ∃ CF > 0,
    (∀ z : E, ‖z - a‖ ≤ r → z ≠ a → F a < F z) ∧
    ∀ p x : E, ‖p - a‖ ≤ ρ → ‖x - a‖ ≤ ρ → p ≠ x →
      (∀ n, ‖bbCurrent rule G p x n - a‖ ≤ r) ∧
      (∀ n, ‖bbCurrent rule G p x n - a‖ ≤ Ce * γ ^ n * max ‖p - a‖ ‖x - a‖) ∧
      (∀ n, ‖G (bbCurrent rule G p x n)‖ ≤ Cg * γ ^ n * max ‖p - a‖ ‖x - a‖) ∧
      (∀ n, 0 ≤ F (bbCurrent rule G p x n) - F a ∧
        F (bbCurrent rule G p x n) - F a ≤ CF * γ ^ (2 * n) * (max ‖p - a‖ ‖x - a‖) ^ 2) ∧
      (∀ n, bbCurrent rule G p x n ≠ a →
        bbCurrent rule G p x n - bbPrevious rule G p x n ≠ 0 ∧
        G (bbCurrent rule G p x n) ≠ 0 ∧ 0 < bbStep rule G p x n) ∧
      Tendsto (bbCurrent rule G p x) atTop (𝓝 a) ∧
      rootFactor (fun n => ‖bbCurrent rule G p x n - a‖ / max ‖p - a‖ ‖x - a‖) ≤ c ∧
      rootFactor (fun n => ‖G (bbCurrent rule G p x n)‖ / max ‖p - a‖ ‖x - a‖) ≤ c ∧
      rootFactor (fun n => (F (bbCurrent rule G p x n) - F a) / (max ‖p - a‖ ‖x - a‖) ^ 2) ≤ c ^ 2

theorem nonlinear_localization_zero (rule : Rule) (F : E → ℝ) (G : E → E)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (m M γ R : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M * ‖z‖ ^ 2)
    (hG : G 0 = 0) (hstrict : HasStrictFDerivAt G A 0)
    (hγ : rate m M < γ) (hγ1 : γ < 1) (hR : 0 < R)
    (hgrad : ∀ z, ‖z‖ ≤ R → HasGradientAt F (G z) z) :
    LocalGuarantee rule F G 0 (rate m M) γ R := by
  have h := positiveModel_of_order_bounds A hA m M hm hmM hbounds
  have hc : 0 ≤ rate m M := div_nonneg (sub_nonneg.mpr hmM) (add_nonneg h.M_pos.le hm.le)
  have hc1 : rate m M < 1 := by
    unfold rate
    exact (div_lt_one (add_pos h.M_pos hm)).mpr (by linarith only [hm])
  obtain ⟨r, hr, hrR, ρ, hρ, hρr, K, hK, hmin, hlocal⟩ :=
    h.local_objective_convergence rule F G hG hstrict (rate m M) γ R hc hc1 hγ hγ1 hR hgrad
      (fun β hβ => hilbert_frozen_envelope A hA rule m M β hm hmM hbounds hβ)
  have hK0 : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hCg : 0 < M + m / 2 := add_pos h.M_pos (div_pos hm (by norm_num))
  refine ⟨r, hr, hrR, ρ, hρ, hρr, K, hK0, (M + m / 2) * K, mul_pos hCg hK0,
    ((M + m / 2) / 2) * K ^ 2, mul_pos (div_pos hCg (by norm_num)) (sq_pos_of_pos hK0), ?_, ?_⟩
  · simpa only [sub_zero] using hmin
  · simpa only [sub_zero] using hlocal

/-- The manuscript's local nonlinear theorem on an arbitrary real Hilbert space.
Only actual selfadjoint positive derivative bounds, strict differentiability,
and the actual gradient relation are hypotheses. -/
theorem nonlinear_localization (rule : Rule) (F : E → ℝ) (G : E → E) (a : E)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (m M γ R : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M * ‖z‖ ^ 2)
    (hG : G a = 0) (hstrict : HasStrictFDerivAt G A a)
    (hγ : rate m M < γ) (hγ1 : γ < 1) (hR : 0 < R)
    (hgrad : ∀ z, ‖z - a‖ ≤ R → HasGradientAt F (G z) z) :
    LocalGuarantee rule F G a (rate m M) γ R := by
  let F' : E → ℝ := fun z => F (a + z)
  let G' : E → E := fun z => G (a + z)
  have hG' : G' 0 = 0 := by simpa only [G', add_zero] using hG
  have hstrict' : HasStrictFDerivAt G' A 0 := strict_derivative_translate G A a hstrict
  have hgrad' : ∀ z, ‖z‖ ≤ R → HasGradientAt F' (G' z) z := by
    intro z hz
    apply gradient_translate F G a z
    apply hgrad
    simpa only [add_sub_cancel_left] using hz
  obtain ⟨r, hr, hrR, ρ, hρ, hρr, Ce, hCe, Cg, hCg, CF, hCF, hmin, hlocal⟩ :=
    nonlinear_localization_zero rule F' G' A hA m M γ R hm hmM hbounds hG' hstrict' hγ hγ1 hR hgrad'
  simp only [sub_zero] at hmin hlocal
  refine ⟨r, hr, hrR, ρ, hρ, hρr, Ce, hCe, Cg, hCg, CF, hCF, ?_, ?_⟩
  · intro z hz hza
    have hh := hmin (z - a) hz (sub_ne_zero.mpr hza)
    have hz' : a + (z - a) = z := by abel
    simpa only [F', add_zero, hz'] using hh
  · intro p x hp hx hpx
    have hpx' : p - a ≠ x - a := by
      intro he
      exact hpx (sub_left_inj.mp he)
    obtain ⟨hdomain, he, hg, hF, hvalid, hconv, hre, hrg, hrF⟩ := hlocal (p - a) (x - a) hp hx hpx'
    have hcur : ∀ n, bbCurrent rule G' (p - a) (x - a) n = bbCurrent rule G p x n - a :=
      bbCurrent_center rule G a p x
    have hprev : ∀ n, bbPrevious rule G' (p - a) (x - a) n = bbPrevious rule G p x n - a :=
      bbPrevious_center rule G a p x
    have hstep : ∀ n, bbStep rule G' (p - a) (x - a) n = bbStep rule G p x n :=
      bbStep_center rule G a p x
    have htranslated : ∀ n, a + bbCurrent rule G' (p - a) (x - a) n = bbCurrent rule G p x n := by
      intro n
      rw [hcur]
      abel
    have hgc : ∀ n, G' (bbCurrent rule G' (p - a) (x - a) n) = G (bbCurrent rule G p x n) := by
      intro n
      exact congrArg G (htranslated n)
    have hfc : ∀ n, F' (bbCurrent rule G' (p - a) (x - a) n) = F (bbCurrent rule G p x n) := by
      intro n
      exact congrArg F (htranslated n)
    have hFzero : F' 0 = F a := by simp only [F', add_zero]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [hcur] using hdomain
    · simpa only [hcur] using he
    · simpa only [hgc] using hg
    · simpa only [hfc, hFzero] using hF
    · intro n hne
      have hn : bbCurrent rule G' (p - a) (x - a) n ≠ 0 := by
        rw [hcur]
        exact sub_ne_zero.mpr hne
      have hh := hvalid n hn
      have hs : bbCurrent rule G' (p - a) (x - a) n - bbPrevious rule G' (p - a) (x - a) n =
          bbCurrent rule G p x n - bbPrevious rule G p x n := by rw [hcur, hprev]; abel
      simpa only [hs, hgc, hstep] using hh
    · have ht : Tendsto (fun n => a + bbCurrent rule G' (p - a) (x - a) n) atTop (𝓝 a) := by
        simpa only [add_zero] using tendsto_const_nhds.add hconv
      simpa only [htranslated] using ht
    · simpa only [hcur] using hre
    · simpa only [hgc] using hrg
    · simpa only [hfc, hFzero] using hrF

/-- Enlarging the prescribed containing neighborhood preserves a local guarantee. -/
theorem LocalGuarantee.mono_radius {rule : Rule} {F : E → ℝ} {G : E → E} {a : E}
    {c γ R S : ℝ} (h : LocalGuarantee rule F G a c γ R) (hRS : R ≤ S) :
    LocalGuarantee rule F G a c γ S := by
  obtain ⟨r, hr, hrR, hrest⟩ := h
  exact ⟨r, hr, hrR.trans hRS, hrest⟩

/-- The source theorem's unrestricted-tail quantifier: any well-defined
trajectory converging to the stationary point has all three sharp root bounds. -/
theorem nonlinear_convergent_rootFactors (rule : Rule) (F : E → ℝ) (G : E → E) (a : E)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (m M R : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M * ‖z‖ ^ 2)
    (hG : G a = 0) (hstrict : HasStrictFDerivAt G A a) (hR : 0 < R)
    (hgrad : ∀ z, ‖z - a‖ ≤ R → HasGradientAt F (G z) z)
    (p x : E) (hconv : Tendsto (bbCurrent rule G p x) atTop (𝓝 a))
    (hregular : ∀ n, bbCurrent rule G p x n ≠ a →
      bbPrevious rule G p x n ≠ bbCurrent rule G p x n)
    (R0 : ℝ) (hR0 : 0 < R0) :
    (∀ᶠ n in atTop, 0 ≤ F (bbCurrent rule G p x n) - F a) ∧
      rootFactor (fun n => ‖bbCurrent rule G p x n - a‖ / R0) ≤ rate m M ∧
      rootFactor (fun n => ‖G (bbCurrent rule G p x n)‖ / R0) ≤ rate m M ∧
      rootFactor (fun n => (F (bbCurrent rule G p x n) - F a) / R0 ^ 2) ≤ (rate m M) ^ 2 := by
  let F' : E → ℝ := fun z => F (a + z)
  let G' : E → E := fun z => G (a + z)
  have hG' : G' 0 = 0 := by simpa only [G', add_zero] using hG
  have hstrict' : HasStrictFDerivAt G' A 0 := strict_derivative_translate G A a hstrict
  have hgrad' : ∀ z, ‖z‖ ≤ R → HasGradientAt F' (G' z) z := by
    intro z hz
    apply gradient_translate F G a z
    apply hgrad
    simpa only [add_sub_cancel_left] using hz
  have hcur : ∀ n, bbCurrent rule G' (p - a) (x - a) n = bbCurrent rule G p x n - a :=
    bbCurrent_center rule G a p x
  have hprev : ∀ n, bbPrevious rule G' (p - a) (x - a) n = bbPrevious rule G p x n - a :=
    bbPrevious_center rule G a p x
  have htranslated : ∀ n, a + bbCurrent rule G' (p - a) (x - a) n = bbCurrent rule G p x n := by
    intro n
    rw [hcur]
    abel
  have hgc : ∀ n, G' (bbCurrent rule G' (p - a) (x - a) n) = G (bbCurrent rule G p x n) := by
    intro n
    exact congrArg G (htranslated n)
  have hfc : ∀ n, F' (bbCurrent rule G' (p - a) (x - a) n) = F (bbCurrent rule G p x n) := by
    intro n
    exact congrArg F (htranslated n)
  have hFzero : F' 0 = F a := by simp only [F', add_zero]
  have hconv' : Tendsto (bbCurrent rule G' (p - a) (x - a)) atTop (𝓝 0) := by
    have ht := hconv.sub_const a
    have hf : bbCurrent rule G' (p - a) (x - a) = fun n => bbCurrent rule G p x n - a := funext hcur
    rw [hf]
    simpa only [sub_self] using ht
  have hregular' : ∀ n, bbCurrent rule G' (p - a) (x - a) n ≠ 0 →
      bbPrevious rule G' (p - a) (x - a) n ≠ bbCurrent rule G' (p - a) (x - a) n := by
    intro n hn he
    have hn' : bbCurrent rule G p x n ≠ a := by
      intro hz
      apply hn
      rw [hcur, hz, sub_self]
    rw [hprev, hcur] at he
    exact hregular n hn' (sub_left_inj.mp he)
  have h := positiveModel_of_order_bounds A hA m M hm hmM hbounds
  have hc : 0 ≤ rate m M := div_nonneg (sub_nonneg.mpr hmM) (add_nonneg h.M_pos.le hm.le)
  have hc1 : rate m M < 1 := by
    unfold rate
    exact (div_lt_one (add_pos h.M_pos hm)).mpr (by linarith only [hm])
  have hh := h.convergent_objective_rootFactors rule F' G' hG' hstrict' (rate m M) R hc hc1 hR hgrad'
    (fun β hβ => hilbert_frozen_envelope A hA rule m M β hm hmM hbounds hβ)
    (p - a) (x - a) hconv' hregular' R0 hR0
  simp only [hgc, hfc, hFzero] at hh
  simpa only [hcur] using hh

/-- Twice continuous Fréchet differentiability near the stationary point gives
the strict-gradient hypothesis and a neighborhood with the actual gradient.
No locally Lipschitz Hessian assumption is used. -/
theorem nonlinear_localization_C2 (rule : Rule) (F : E → ℝ) (a : E)
    (hF : ContDiffAt ℝ 2 F a) (hG : gradient F a = 0) (m M γ R : ℝ)
    (hA : (fderiv ℝ (gradient F) a).toLinearMap.IsSymmetric)
    (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m * ‖z‖ ^ 2 ≤ inner (𝕜 := ℝ) z ((fderiv ℝ (gradient F) a) z) ∧
      inner (𝕜 := ℝ) z ((fderiv ℝ (gradient F) a) z) ≤ M * ‖z‖ ^ 2)
    (hγ : rate m M < γ) (hγ1 : γ < 1) (hR : 0 < R) :
    LocalGuarantee rule F (gradient F) a (rate m M) γ R := by
  have hdiff : ∀ᶠ z in 𝓝 a, DifferentiableAt ℝ F z :=
    hF.eventually.mono (fun z hz => hz.differentiableAt (by norm_num))
  obtain ⟨b, hb, hball⟩ := Metric.eventually_nhds_iff.mp hdiff
  let R' := min R (b / 2)
  have hR' : 0 < R' := lt_min hR (div_pos hb (by norm_num))
  have hR'R : R' ≤ R := min_le_left _ _
  have hgrad : ∀ z, ‖z - a‖ ≤ R' → HasGradientAt F (gradient F z) z := by
    intro z hz
    apply DifferentiableAt.hasGradientAt
    apply hball
    rw [dist_eq_norm]
    exact (hz.trans (min_le_right _ _)).trans_lt (by linarith only [hb])
  exact (nonlinear_localization rule F (gradient F) a (fderiv ℝ (gradient F) a) hA m M γ R'
    hm hmM hbounds hG (c2_gradient_strict F a hF) hγ hγ1 hR' hgrad).mono_radius hR'R

end BB.Nonlinear
