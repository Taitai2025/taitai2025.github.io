import BB.NonlinearMain
import BB.NonlinearAssumptions

/-!
# Uniform nonlinear tracking for a common two-point modulus

Every radius and arithmetic constant is selected before the gradient map.
The modulus is only required to tend to zero from positive radii; no monotonicity
or differentiability of a family parameter is assumed.
-/

noncomputable section
namespace BB.Nonlinear
open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A shared quantitative strict-linearization bound around a stationary center. -/
def CommonModulus (G : E → E) (A : E →L[ℝ] E) (a : E) (ω : ℝ → ℝ) (R : ℝ) : Prop :=
  ∀ r ∈ Ioc (0 : ℝ) R, ∀ x, ‖x-a‖ ≤ r → ∀ y, ‖y-a‖ ≤ r →
    ‖G x - G y - A (x-y)‖ ≤ ω r * ‖x-y‖

lemma common_modulus_small_radius (ω : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0)) (ε : ℝ) (hε : 0 < ε) :
    ∃ r > 0, r ≤ R ∧ ω r ≤ ε := by
  have he : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), ω r < ε := hlim (eventually_lt_nhds hε)
  have hp : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), 0 < r := self_mem_nhdsWithin
  have hb : ∀ᶠ r in nhdsWithin (0 : ℝ) (Ioi 0), r < R :=
    (eventually_lt_nhds hR).filter_mono nhdsWithin_le_nhds
  obtain ⟨r, hr, hrR, he⟩ := (hp.and (hb.and he)).exists
  exact ⟨r, hr, hrR.le, he.le⟩

/-- A common modulus supplies the actual strict Fréchet derivative for each map. -/
theorem CommonModulus.hasStrictFDerivAt (G : E → E) (A : E →L[ℝ] E) (a : E)
    (ω : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0)) (hmod : CommonModulus G A a ω R) :
    HasStrictFDerivAt G A a := by
  apply strict_derivative_of_closed_ball_estimates
  intro ε hε
  obtain ⟨r, hr, hrR, hω⟩ := common_modulus_small_radius ω R hR hlim ε hε
  refine ⟨r, hr, ?_⟩
  intro x hx y hy
  have h := hmod r ⟨hr, hrR⟩ x
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx) y
    (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hy)
  exact h.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))

lemma CommonModulus.translate (G : E → E) (A : E →L[ℝ] E) (a : E)
    (ω : ℝ → ℝ) (R : ℝ) (hmod : CommonModulus G A a ω R) :
    CommonModulus (fun z => G (a+z)) A 0 ω R := by
  intro r hr x hx y hy
  simp only [sub_zero] at hx hy
  have h := hmod r hr (a+x) (by simpa only [add_sub_cancel_left] using hx)
    (a+y) (by simpa only [add_sub_cancel_left] using hy)
  have heq : (a+x)-(a+y)=x-y := by abel
  simpa only [heq] using h

variable {A : E →L[ℝ] E} {m M : ℝ}

/-- Uniform finite tracking: D and r precede every gradient map with the shared modulus. -/
theorem PositiveModel.uniform_finite_horizon_tracking (h : PositiveModel A m M) (rule : Rule)
    (ω : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0))
    (N : ℕ) (τ η : ℝ) (hτ : 0 < τ) (hη : 0 < η) :
    ∃ D ≥ 1, ∃ r > 0, r ≤ R ∧ ∀ (G : E → E), G 0 = 0 → CommonModulus G A 0 ω R →
      ∀ p x : E, ‖p‖ ≤ r → ‖x‖ ≤ r → p ≠ x → x ≠ 0 →
      ∀ q ≤ N, (∀ j < q, τ * ‖x‖ ≤ ‖bbCurrent rule A p x j‖) →
      (∀ j ≤ q, ‖bbCurrent rule G p x j - bbCurrent rule A p x j‖ ≤ η * ‖x‖ ∧
        ‖bbCurrent rule G p x j‖ + ‖bbCurrent rule A p x j‖ ≤ D * ‖x‖) ∧
      (∀ j < q, bbCurrent rule G p x j - bbPrevious rule G p x j ≠ 0 ∧
        G (bbCurrent rule G p x j) ≠ 0 ∧ 0 < bbStep rule G p x j) := by
  obtain ⟨D, S, hD, hDpow, hS, hSbound⟩ := h.tracking_constants N τ hτ
  have hm := h.m_pos
  have hM := h.M_pos
  have hDp : 0 < D+1 := by linarith only [hD]
  have hSp : 0 < S^N := pow_pos (zero_lt_one.trans_le hS) N
  let d := m*τ/M
  have hd : 0 < d := div_pos (mul_pos hm hτ) hM
  let σ := min 1 (min (τ/2) (d/4))
  have _hσ : 0 < σ := by dsimp [σ]; positivity
  let Ω := min (m/2) (min (σ/S^N) (η/S^N))
  have hΩ : 0 < Ω := by dsimp [Ω]; positivity
  have hΩhalf : Ω ≤ m/2 := min_le_left _ _
  have hΩσ : Ω*S^N ≤ σ :=
    (le_div_iff hSp).mp ((min_le_right _ _).trans (min_le_left _ _))
  have hΩη : Ω*S^N ≤ η :=
    (le_div_iff hSp).mp ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨b, hb, hbR, hω⟩ := common_modulus_small_radius ω R hR hlim Ω hΩ
  let r := b/(D+1)
  have hr : 0 < r := div_pos hb hDp
  have hCr : (D+1)*r=b := by dsimp [r]; field_simp
  have hrb : r ≤ b := by nlinarith only [hCr, hD, hr]
  refine ⟨2*D+1, by linarith only [hD], r, hr, hrb.trans hbR, ?_⟩
  intro G hG hmod p x hp hx hpx hx0 q hq hpre
  have hrem : ∀ u, ‖u‖ ≤ (D+1)*r → ∀ v, ‖v‖ ≤ (D+1)*r →
      ‖G u-G v-A (u-v)‖ ≤ Ω*‖u-v‖ := by
    intro u hu v hv
    rw [hCr] at hu hv
    have he := hmod b ⟨hb, hbR⟩ u (by simpa only [sub_zero] using hu)
      v (by simpa only [sub_zero] using hv)
    exact he.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _))
  have hex := h.finite_tracking_explicit rule G p x N q τ r Ω D S d hτ hr hΩ.le hΩhalf
    hD hDpow hS hd rfl hSbound hΩσ hG hrem hp hx hpx hx0 hq hpre
  refine ⟨?_, hex.2⟩
  intro j hj
  refine ⟨?_, (hex.1 j hj).2⟩
  apply (hex.1 j hj).1.trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg x)
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_right hS (by omega : j ≤ N)) hΩ.le).trans hΩη

/-- The block property used by the actual restart induction. -/
def BlockGuarantee (rule : Rule) (G : E → E) (γ : ℝ) (N : ℕ) (D r : ℝ) : Prop :=
  ∀ p x : E, ‖p‖ ≤ r → ‖x‖ ≤ r → (x=0 ∨ p≠x) →
    ∃ q, 1 ≤ q ∧ q ≤ N ∧ ‖bbCurrent rule G p x q‖ ≤ γ^q*‖x‖ ∧
      (∀ j ≤ q, ‖bbCurrent rule G p x j‖ ≤ D*‖x‖) ∧
      (bbCurrent rule G p x q=0 ∨ bbPrevious rule G p x q≠bbCurrent rule G p x q) ∧
      (∀ j<q, bbCurrent rule G p x j≠0 →
        bbCurrent rule G p x j-bbPrevious rule G p x j≠0 ∧
        G (bbCurrent rule G p x j)≠0 ∧ 0<bbStep rule G p x j)

/-- A common modulus supplies common contracting-block constants and a common radius. -/
theorem PositiveModel.uniform_contracting_blocks (h : PositiveModel A m M) (rule : Rule)
    (ω : ℝ → ℝ) (R : ℝ) (hR : 0 < R)
    (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0))
    (β γ C : ℝ) (hβ : 0 < β) (hβγ : β < γ) (hγ1 : γ < 1) (hC : 1 ≤ C)
    (hquad : QuadraticEnvelope rule A β C) :
    ∃ N ≥ 1, ∃ D ≥ 1, ∃ r > 0, r ≤ R ∧
      ∀ G : E → E, G 0=0 → CommonModulus G A 0 ω R → BlockGuarantee rule G γ N D r := by
  have hγ : 0 < γ := hβ.trans hβγ
  obtain ⟨N, hN, hNrate⟩ := exists_comparison_horizon β γ C hβ hβγ hC
  let τ := γ^N/4
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hγNle : γ^N ≤ 1 := by simpa using pow_le_pow_of_le_one hγ.le hγ1.le (Nat.zero_le N)
  have hτ1 : τ < 1 := by dsimp [τ]; linarith only [hγNle]
  obtain ⟨D, hD, r, hr, hrR, htrack⟩ :=
    h.uniform_finite_horizon_tracking rule ω R hR hlim N τ (τ/2) hτ (by positivity)
  refine ⟨N, hN, D, hD, r, hr, hrR, ?_⟩
  intro G hG hmod p x hp hx hregular
  by_cases hx0 : x=0
  · subst x
    refine ⟨1, le_rfl, hN, ?_, ?_, Or.inl ?_, ?_⟩
    · simp [bbCurrent_zero_initial rule G hG]
    · intro j _
      simp [bbCurrent_zero_initial rule G hG]
    · exact bbCurrent_zero_initial rule G hG p 1
    · intro j _ hj
      exact False.elim (hj (bbCurrent_zero_initial rule G hG p j))
  · have hpx : p≠x := hregular.resolve_left hx0
    have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hatN : ‖bbCurrent rule A p x N‖ ≤ τ*‖x‖ :=
      (hquad p x hpx N).trans (mul_le_mul_of_nonneg_right hNrate hxpos.le)
    have hex : ∃ q, ‖bbCurrent rule A p x q‖ ≤ τ*‖x‖ := ⟨N,hatN⟩
    let q := Nat.find hex
    have hhit : ‖bbCurrent rule A p x q‖ ≤ τ*‖x‖ := Nat.find_spec hex
    have hqN : q≤N := Nat.find_min' hex hatN
    have hqpos : 0<q := by
      by_contra hq
      have hz : q=0 := by omega
      rw [hz, bbCurrent_zero] at hhit
      have hpos := mul_pos (sub_pos.mpr hτ1) hxpos
      nlinarith only [hhit,hpos]
    have hpre : ∀ j<q, τ*‖x‖ ≤ ‖bbCurrent rule A p x j‖ := by
      intro j hj
      exact (lt_of_not_ge (Nat.find_min hex hj)).le
    have ht := htrack G hG hmod p x hp hx hpx hx0 q hqN hpre
    have hcontract : ‖bbCurrent rule G p x q‖ ≤ γ^q*‖x‖ := by
      have he := (ht.1 q le_rfl).1
      have hn := norm_sub_norm_le (bbCurrent rule G p x q) (bbCurrent rule A p x q)
      have hpowR := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hγ.le hγ1.le hqN) hxpos.le
      have hnonneg := mul_nonneg (pow_nonneg hγ.le N) hxpos.le
      dsimp [τ] at he hhit
      nlinarith only [he, hn, hhit, hpowR, hnonneg]
    have hlast : bbCurrent rule G p x q-bbPrevious rule G p x q≠0 := by
      have heq : q=(q-1)+1 := by omega
      have hv := ht.2 (q-1) (by omega)
      rw [heq, bb_secant_succ]
      exact smul_ne_zero (neg_ne_zero.mpr hv.2.2.ne') hv.2.1
    refine ⟨q,hqpos,hqN,hcontract,?_,Or.inr (Ne.symm (sub_ne_zero.mp hlast)),?_⟩
    · intro j hj
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (ht.1 j hj).2
    · intro j hj _
      exact ht.2 j hj

end BB.Nonlinear
