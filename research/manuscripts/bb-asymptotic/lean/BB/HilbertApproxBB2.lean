import BB.HilbertApproxOrbit
import BB.HilbertWeightedSharpness

/-!
# Optimal uniform BB2 rates without endpoint eigenvectors

The approximate endpoint starts use amplitudes `sqrt b` and `sqrt a`, giving
asymptotic BB2 balance. The proof works directly with `A`, without assuming the
existence of a square-root operator or a spectral-measure representation.
-/

noncomputable section
namespace BB
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

lemma approximate_combination_bb2_quotient_limit (A : E →L[ℝ] E) (a b : ℝ) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0))
    (hpq : Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0)) (u v : ℝ)
    (hD : a^2*u^2+b^2*v^2 ≠ 0) (x : ℕ → E)
    (hx : Tendsto (fun j => x j-(u•p j+v•q j)) atTop (𝓝 0)) :
    Tendsto (fun j => operatorBB2 A.toLinearMap (x j)) atTop
      (𝓝 (bb2Two a b u v)) := by
  have hn := approximate_combination_norm_limit p q hp hq hpq u v
  have he := approximate_combination_energy_limit A a b p q hp hq hep heq hpq u v
  have hex := inner_continuous_apply_error_zero A x (fun j => u•p j+v•q j) _ hx hn
  have hnum : Tendsto (fun j => ⟪x j,A (x j)⟫) atTop (𝓝 (a*u^2+b*v^2)) := by
    simpa only [sub_add_cancel, zero_add] using hex.add he
  have heA : Tendsto (fun j => A (x j-(u•p j+v•q j))) atTop (𝓝 0) := by
    simpa only [map_zero] using A.continuous.continuousAt.tendsto.comp hx
  have hres : Tendsto (fun j => A (u•p j+v•q j)-((a*u)•p j+(b*v)•q j)) atTop (𝓝 0) := by
    have hid (j : ℕ) : A (u•p j+v•q j)-((a*u)•p j+(b*v)•q j) =
        u•(A (p j)-a•p j)+v•(A (q j)-b•q j) := by
      simp only [map_add, map_smul, smul_sub, smul_smul]
      rw [mul_comm u a, mul_comm v b]; abel
    simpa only [hid, smul_zero, zero_add] using (hep.const_smul u).add (heq.const_smul v)
  have hAx : Tendsto (fun j => A (x j)-((a*u)•p j+(b*v)•q j)) atTop (𝓝 0) := by
    simpa only [map_sub, sub_add_sub_cancel, zero_add] using heA.add hres
  have hnA := norm_limit_of_error_zero (fun j => A (x j))
    (fun j => (a*u)•p j+(b*v)•q j) _ hAx
    (approximate_combination_norm_limit p q hp hq hpq (a*u) (b*v))
  have hden : Tendsto (fun j => ‖A (x j)‖^2) atTop (𝓝 (a^2*u^2+b^2*v^2)) := by
    have ht := hnA.pow 2
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg (a*u)) (sq_nonneg (b*v)))] at ht
    simpa only [mul_pow] using ht
  exact hnum.div hden hD

lemma approximate_bb2_endpoint_quotient_limit (A : E →L[ℝ] E) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0))
    (hpq : Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0)) (k : ℕ) (x : ℕ → E)
    (hx : Tendsto (fun j => x j-hilbertEndpointOrbit a b (Real.sqrt b•p j) (Real.sqrt a•q j) k)
      atTop (𝓝 0)) :
    Tendsto (fun j => operatorBB2 A.toLinearMap (x j)) atTop (𝓝 (2/(a+b))) := by
  have hb := ha.trans hab
  let u := (rate a b)^k*Real.sqrt b
  let v := (-(rate a b))^k*Real.sqrt a
  have hu : 0 < u := mul_pos (pow_pos (rate_pos ha hab) _) (Real.sqrt_pos.mpr hb)
  have hbal : a*u^2 = b*v^2 := by
    have hneg : ((-(rate a b))^k)^2 = ((rate a b)^k)^2 := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul, neg_sq,
        ← pow_mul, Nat.mul_comm 2 k, pow_mul]
    dsimp [u,v]
    rw [mul_pow, mul_pow, Real.sq_sqrt hb.le, Real.sq_sqrt ha.le, hneg]
    ring
  have hD : a^2*u^2+b^2*v^2 ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg
    (mul_pos (sq_pos_of_pos ha) (sq_pos_of_pos hu)) (mul_nonneg (sq_nonneg b) (sq_nonneg v)))
  have hbb := weighted_balanced_bb2_step ha hb hu.ne' hbal
  have hlim := approximate_combination_bb2_quotient_limit A a b p q hp hq hep heq hpq u v hD x
    (by simpa only [hilbertEndpointOrbit, smul_smul] using hx)
  rwa [hbb] at hlim

def matchedBB2Pair (A : E →L[ℝ] E) (x : E) : ℕ → E × E
  | 0 => (x,x)
  | n+1 => let z := matchedBB2Pair A x n
      (z.2,operatorGradientStep A.toLinearMap (operatorBB2 A.toLinearMap z.1) z.2)

def matchedBB2Orbit (A : E →L[ℝ] E) (x : E) (n : ℕ) : E := (matchedBB2Pair A x n).2

@[simp] theorem matchedBB2Orbit_zero (A : E →L[ℝ] E) (x : E) : matchedBB2Orbit A x 0 = x := rfl

@[simp] theorem matchedBB2Orbit_one (A : E →L[ℝ] E) (x : E) :
    matchedBB2Orbit A x 1 = operatorGradientStep A.toLinearMap (operatorBB2 A.toLinearMap x) x := rfl

theorem matchedBB2Orbit_update (A : E →L[ℝ] E) (x : E) (n : ℕ) :
    matchedBB2Orbit A x (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB2 A.toLinearMap (matchedBB2Orbit A x n)) (matchedBB2Orbit A x (n+1)) := rfl

lemma scaled_approximate_eigenvector_error (A : E →L[ℝ] E) (a s : ℝ) (p : ℕ → E)
    (hp : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0)) :
    Tendsto (fun j => A (s•p j)-a•(s•p j)) atTop (𝓝 0) := by
  have he (j : ℕ) : A (s•p j)-a•(s•p j) = s•(A (p j)-a•p j) := by
    simp only [map_smul, smul_sub, smul_smul]; rw [mul_comm a s]
  simpa only [he, smul_zero] using hp.const_smul s

theorem approximate_bb2_endpoint_matched_pair (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => (matchedBB2Pair A (Real.sqrt b•p j+Real.sqrt a•q j) k).1 -
      hilbertEndpointOrbit a b (Real.sqrt b•p j) (Real.sqrt a•q j) (k-1)) atTop (𝓝 0) ∧
    Tendsto (fun j => (matchedBB2Pair A (Real.sqrt b•p j+Real.sqrt a•q j) k).2 -
      hilbertEndpointOrbit a b (Real.sqrt b•p j) (Real.sqrt a•q j) k) atTop (𝓝 0) := by
  have hpq := approximate_eigenvectors_inner_zero A hA a b hab.ne p q hp hq hep heq
  induction k with
  | zero => simp only [matchedBB2Pair, hilbertEndpointOrbit, pow_zero, one_smul,
      Nat.zero_sub, sub_self]; exact ⟨tendsto_const_nhds,tendsto_const_nhds⟩
  | succ k ih =>
    refine ⟨?_,?_⟩
    · simpa only [matchedBB2Pair, Nat.add_sub_cancel] using ih.2
    · have hα := approximate_bb2_endpoint_quotient_limit A a b ha hab p q hp hq hep heq hpq
        (k-1) (fun j => (matchedBB2Pair A (Real.sqrt b•p j+Real.sqrt a•q j) k).1) ih.1
      have hn := approximate_combination_norm_limit p q hp hq hpq
        ((rate a b)^k*Real.sqrt b) ((-(rate a b))^k*Real.sqrt a)
      have hstep := operator_step_error_zero A
        (fun j => (matchedBB2Pair A (Real.sqrt b•p j+Real.sqrt a•q j) k).2)
        (fun j => hilbertEndpointOrbit a b (Real.sqrt b•p j) (Real.sqrt a•q j) k) _ (2/(a+b))
        (fun j => operatorBB2 A.toLinearMap (matchedBB2Pair A (Real.sqrt b•p j+Real.sqrt a•q j) k).1)
        ih.2 (by simpa only [hilbertEndpointOrbit, smul_smul] using hn) hα
      have href := approximate_endpoint_reference_step A a b ha hab
        (fun j => Real.sqrt b•p j) (fun j => Real.sqrt a•q j)
        (scaled_approximate_eigenvector_error A a (Real.sqrt b) p hep)
        (scaled_approximate_eigenvector_error A b (Real.sqrt a) q heq) k
      simpa only [matchedBB2Pair, sub_add_sub_cancel, zero_add] using hstep.add href

theorem approximate_bb2_endpoint_matched_norm_limit (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => ‖matchedBB2Orbit A (Real.sqrt b•p j+Real.sqrt a•q j) k‖) atTop
      (𝓝 ((rate a b)^k*Real.sqrt (a+b))) := by
  have hpq := approximate_eigenvectors_inner_zero A hA a b hab.ne p q hp hq hep heq
  have hn := approximate_combination_norm_limit p q hp hq hpq
    ((rate a b)^k*Real.sqrt b) ((-(rate a b))^k*Real.sqrt a)
  have hval : Real.sqrt (((rate a b)^k*Real.sqrt b)^2+((-(rate a b))^k*Real.sqrt a)^2) =
      (rate a b)^k*Real.sqrt (a+b) := by
    simpa only [normTwo, Real.sq_sqrt ha.le, Real.sq_sqrt (ha.trans hab).le, add_comm b a] using
      endpoint_norm_orbit (rate_pos ha hab).le (Real.sqrt b) (Real.sqrt a) k
  rw [hval] at hn
  apply norm_limit_of_error_zero _ _ _
    (approximate_bb2_endpoint_matched_pair A hA a b ha hab p q hp hq hep heq k).2
  simpa only [hilbertEndpointOrbit, smul_smul] using hn

theorem approximate_bb2_endpoint_matched_ratio_limit (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => ‖matchedBB2Orbit A (Real.sqrt b•p j+Real.sqrt a•q j) k‖ /
      ‖Real.sqrt b•p j+Real.sqrt a•q j‖) atTop (𝓝 ((rate a b)^k)) := by
  have hn := approximate_bb2_endpoint_matched_norm_limit A hA a b ha hab p q hp hq hep heq k
  have h0 := approximate_bb2_endpoint_matched_norm_limit A hA a b ha hab p q hp hq hep heq 0
  have hs : Real.sqrt (a+b) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by linarith))
  simpa only [matchedBB2Orbit_zero, pow_zero, one_mul, mul_div_cancel_right₀ _ hs] using
    hn.div (by simpa only [matchedBB2Orbit_zero, pow_zero, one_mul] using h0) hs

/-- Any fixed-operator uniform matched BB2 rate is at least the spectral rate,
even if both endpoint eigenspaces are trivial. -/
theorem hilbert_bb2_spectral_uniform_rate_ge [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 ≤ γ)
    (henv : ∀ x : E, x ≠ 0 → ∀ k, ‖matchedBB2Orbit A x k‖ ≤ C*γ^k*‖x‖) :
    rate a b ≤ γ := by
  obtain ⟨p,q,hpq,hepN,heqN⟩ := spectrum_approximate_endpoint_sequences A hA a b hab.le hbounds haspec hbspec
  have hp : ∀ j, ‖p j‖ = 1 := fun j => (hpq j).1
  have hq : ∀ j, ‖q j‖ = 1 := fun j => (hpq j).2
  have hep := tendsto_zero_iff_norm_tendsto_zero.mpr hepN
  have heq := tendsto_zero_iff_norm_tendsto_zero.mpr heqN
  have hs : 0 < Real.sqrt (a+b) := Real.sqrt_pos.mpr (by linarith)
  have h0 : Tendsto (fun j => ‖Real.sqrt b•p j+Real.sqrt a•q j‖) atTop (𝓝 (Real.sqrt (a+b))) := by
    simpa only [matchedBB2Orbit_zero, pow_zero, one_mul] using
      approximate_bb2_endpoint_matched_norm_limit A hA a b ha hab p q hp hq hep heq 0
  have hpos : ∀ᶠ j in atTop, 0 < ‖Real.sqrt b•p j+Real.sqrt a•q j‖ :=
    h0.eventually (eventually_gt_nhds hs)
  have hpow : ∀ k : ℕ, (rate a b)^k ≤ C*γ^k := by
    intro k
    apply le_of_tendsto (approximate_bb2_endpoint_matched_ratio_limit A hA a b ha hab p q hp hq hep heq k)
    filter_upwards [hpos] with j hj
    exact (div_le_iff hj).mpr (henv _ (norm_pos_iff.mp hj) k)
  have hroot := rootFactor_le_of_envelope (fun k => (rate a b)^k)
    (fun k => pow_nonneg (rate_pos ha hab).le k) γ hγ ⟨C,hC,hpow⟩
  have hval : rootFactor (fun k => (rate a b)^k) = rate a b := by
    simpa only [one_mul] using rootFactor_geometric 1 (rate a b) zero_lt_one (rate_pos ha hab).le
  rwa [hval] at hroot

def MatchedBB2UniformRates (A : E →L[ℝ] E) : Set ℝ :=
  {γ | 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : E, x ≠ 0 → ∀ k,
    ‖matchedBB2Orbit A x k‖ ≤ C*γ^k*‖x‖}

theorem hilbert_bb2_matched_uniform_rates_isGLB [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    IsGLB (MatchedBB2UniformRates A) (rate a b) := by
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hupper : ∀ γ : ℝ, rate a b < γ → γ ∈ MatchedBB2UniformRates A := by
    intro γ hγ
    obtain ⟨C,hC,henv⟩ := bb2_matched_uniform_family_envelope a b γ ha hab hγ
    refine ⟨hc.trans_lt hγ,C,hC,?_⟩
    intro x hx k
    exact henv E A hA hbounds (matchedBB2Orbit A x) hx (matchedBB2Orbit_one A x)
      (matchedBB2Orbit_update A x) k
  constructor
  · intro γ hγ
    rcases hγ with ⟨hγpos,C,hC,henv⟩
    rcases hab.lt_or_eq with hablt | habeq
    · exact hilbert_bb2_spectral_uniform_rate_ge A hA a b ha hablt hbounds haspec hbspec
        C γ hC hγpos.le henv
    · subst b
      simpa only [rate, sub_self, zero_div] using hγpos.le
  · intro d hd
    apply le_of_forall_strict_upper_bound
    intro γ hγ
    exact hd (hupper γ hγ)

end BB
