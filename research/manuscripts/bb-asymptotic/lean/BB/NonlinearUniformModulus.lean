import BB.NonlinearUniformTracking

/-!
# Local BB constants uniform over every objective with a shared modulus

All radii and envelope constants are quantified before the center, objective,
and gradient. Their inputs are only the fixed derivative model, containing
radius, common two-point modulus, desired rate and fixed BB rule.
-/

noncomputable section
namespace BB.Nonlinear
open Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {A : E →L[ℝ] E} {m M : ℝ}

/-- Uniform restart envelopes with the gradient map quantified after all constants. -/
theorem PositiveModel.uniform_local_envelope (h : PositiveModel A m M) (rule : Rule)
    (ω : ℝ → ℝ) (R₀ R : ℝ) (hR₀ : 0 < R₀) (hR : 0 < R)
    (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0))
    (β γ C : ℝ) (hβ : 0 < β) (hβγ : β < γ) (hγ1 : γ < 1) (hC : 1 ≤ C)
    (hquad : QuadraticEnvelope rule A β C) :
    ∃ ρ > 0, ρ ≤ R ∧ ∃ K ≥ 1,
      ∀ G : E → E, G 0=0 → CommonModulus G A 0 ω R₀ →
      ∀ p x : E, ‖p‖ ≤ ρ → ‖x‖ ≤ ρ → (x=0 ∨ p≠x) →
        (∀ n, ‖bbCurrent rule G p x n‖ ≤ K*γ^n*‖x‖) ∧
        (∀ n, ‖bbCurrent rule G p x n‖ ≤ R) ∧
        (∀ n, bbCurrent rule G p x n≠0 →
          bbCurrent rule G p x n-bbPrevious rule G p x n≠0 ∧
          G (bbCurrent rule G p x n)≠0 ∧ 0<bbStep rule G p x n) := by
  have hγ : 0<γ := hβ.trans hβγ
  obtain ⟨N,_hN,D,hD,r,hr,_hrR₀,hblocks⟩ :=
    h.uniform_contracting_blocks rule ω R₀ hR₀ hlim β γ C hβ hβγ hγ1 hC hquad
  have hDp : 0<D := zero_lt_one.trans_le hD
  let ρ := min r R/D
  have hρ : 0<ρ := div_pos (lt_min hr hR) hDp
  have hρr : ρ≤r/D := div_le_div_of_nonneg_right (min_le_left r R) hDp.le
  have hρR : ρ≤R/D := div_le_div_of_nonneg_right (min_le_right r R) hDp.le
  have hDρ : D*ρ≤R := by
    have hx := (le_div_iff hDp).mp hρR
    simpa only [mul_comm] using hx
  have hρleR : ρ≤R := by nlinarith only [hDρ,hD,hρ]
  have hpow : γ^N≤1 := by simpa using pow_le_pow_of_le_one hγ.le hγ1.le (Nat.zero_le N)
  have hK : 1≤D/γ^N := (le_div_iff (pow_pos hγ N)).mpr (by nlinarith only [hpow,hD])
  refine ⟨ρ,hρ,hρleR,D/γ^N,hK,?_⟩
  intro G hG hmod p x hp hx hregular
  have hpr : ‖p‖≤r := by
    have hpp := (le_div_iff hDp).mp (hp.trans hρr)
    have hpD := mul_le_mul_of_nonneg_right hD (norm_nonneg p)
    nlinarith only [hpp,hpD]
  have he := fun n => restart_envelope_of_contracting_blocks rule G γ N D r
    hγ hγ1 hD hr (hblocks G hG hmod) n p x hpr (hx.trans hρr) hregular
  refine ⟨fun n => (he n).1, ?_, fun n => (he n).2.2⟩
  intro n
  exact (he n).2.1.trans ((mul_le_mul_of_nonneg_left hx hDp.le).trans hDρ)

/-- Fixed-radius gradient and objective comparisons from an explicit two-point estimate. -/
theorem PositiveModel.fixed_ball_comparisons (h : PositiveModel A m M)
    (F : E → ℝ) (G : E → E) (hG : G 0=0) (r : ℝ) (hr : 0<r)
    (hgrad : ∀ x, ‖x‖≤r → HasGradientAt F (G x) x)
    (hrem : ∀ u, ‖u‖≤r → ∀ v, ‖v‖≤r →
      ‖G u-G v-A (u-v)‖≤(m/2)*‖u-v‖) :
    ∀ x, ‖x‖≤r → (m/2)*‖x‖≤‖G x‖ ∧ ‖G x‖≤(M+m/2)*‖x‖ ∧
      (m/4)*‖x‖^2≤F x-F 0 ∧ F x-F 0≤((M+m/2)/2)*‖x‖^2 := by
  let S := Metric.closedBall (0:E) r
  have hzero : (0:E)∈S := by simpa only [S,Metric.mem_closedBall,dist_self] using hr.le
  have hremS : ∀ u∈S, ∀ v∈S, ‖G u-G v-A (u-v)‖≤(m/2)*‖u-v‖ := by
    intro u hu v hv
    exact hrem u (by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hu)
      v (by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hv)
  have hgradS : ∀ x∈S, HasGradientAt F (G x) x := by
    intro x hx
    exact hgrad x (by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hx)
  intro x hx
  have hxS : x∈S := by simpa only [S,Metric.mem_closedBall,dist_zero_right] using hx
  have hgb := local_gradient_bounds G A S 0 x m M (m/2) hzero hxS hG
    h.coercive h.norm_upper hremS
  have hsegment : ∀ t∈Icc (0:ℝ) 1, (0:E)+t•x∈S := by
    intro t ht
    have hn : ‖t•x‖≤r := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans (by simpa using hx)
    simpa only [zero_add,S,Metric.mem_closedBall,dist_zero_right] using hn
  have hfb := local_objective_bounds F G A S 0 x m M (m/2) hzero hG
    hsegment hgradS h.coercive h.norm_upper hremS
  simp only [sub_zero] at hgb
  simp only [zero_add] at hfb
  refine ⟨?_,hgb.2,?_,hfb.2⟩ <;> nlinarith only [hgb.1,hfb.1]

/-- The complete local conclusions with every numerical constant exposed. -/
def FixedLocalGuarantee (rule : Rule) (F : E → ℝ) (G : E → E) (a : E)
    (c γ r ρ Ce Cg CF : ℝ) : Prop :=
  (∀ z:E, ‖z-a‖≤r → z≠a → F a<F z) ∧
  ∀ p x:E, ‖p-a‖≤ρ → ‖x-a‖≤ρ → p≠x →
    (∀ n, ‖bbCurrent rule G p x n-a‖≤r) ∧
    (∀ n, ‖bbCurrent rule G p x n-a‖≤Ce*γ^n*max ‖p-a‖ ‖x-a‖) ∧
    (∀ n, ‖G (bbCurrent rule G p x n)‖≤Cg*γ^n*max ‖p-a‖ ‖x-a‖) ∧
    (∀ n, 0≤F (bbCurrent rule G p x n)-F a ∧
      F (bbCurrent rule G p x n)-F a≤CF*γ^(2*n)*(max ‖p-a‖ ‖x-a‖)^2) ∧
    (∀ n, bbCurrent rule G p x n≠a →
      bbCurrent rule G p x n-bbPrevious rule G p x n≠0 ∧
      G (bbCurrent rule G p x n)≠0 ∧ 0<bbStep rule G p x n) ∧
    Tendsto (bbCurrent rule G p x) atTop (𝓝 a) ∧
    rootFactor (fun n => ‖bbCurrent rule G p x n-a‖/max ‖p-a‖ ‖x-a‖)≤c ∧
    rootFactor (fun n => ‖G (bbCurrent rule G p x n)‖/max ‖p-a‖ ‖x-a‖)≤c ∧
    rootFactor (fun n => (F (bbCurrent rule G p x n)-F a)/(max ‖p-a‖ ‖x-a‖)^2)≤c^2

/-- Fixed uniform constants directly imply the previously packaged local guarantee. -/
theorem FixedLocalGuarantee.toLocalGuarantee
    {rule : Rule} {F : E → ℝ} {G : E → E} {a : E} {c γ R r ρ Ce Cg CF : ℝ}
    (h : FixedLocalGuarantee rule F G a c γ r ρ Ce Cg CF)
    (hr : 0<r) (hrR : r≤R) (hρ : 0<ρ) (hρr : ρ≤r)
    (hCe : 0<Ce) (hCg : 0<Cg) (hCF : 0<CF) : LocalGuarantee rule F G a c γ R :=
  ⟨r,hr,hrR,ρ,hρ,hρr,Ce,hCe,Cg,hCg,CF,hCF,h⟩

/-- Uniform zero-centered local convergence, with constants before both F and G. -/
theorem nonlinear_uniform_modulus_zero (rule : Rule) (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (m M γ R₀ : ℝ) (hm : 0<m) (hmM : m≤M)
    (hbounds : ∀ z:E, m*‖z‖^2≤inner (𝕜:=ℝ) z (A z) ∧ inner (𝕜:=ℝ) z (A z)≤M*‖z‖^2)
    (ω : ℝ → ℝ) (hR₀ : 0<R₀) (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0))
    (hγ : rate m M<γ) (hγ1 : γ<1) :
    ∃ r>0, r≤R₀ ∧ ∃ ρ>0, ρ≤r ∧ ∃ Ce>0, ∃ Cg>0, ∃ CF>0,
      ∀ (F:E→ℝ) (G:E→E), G 0=0 → CommonModulus G A 0 ω R₀ →
        (∀ z, ‖z‖≤R₀ → HasGradientAt F (G z) z) →
        FixedLocalGuarantee rule F G 0 (rate m M) γ r ρ Ce Cg CF := by
  have h := positiveModel_of_order_bounds A hA m M hm hmM hbounds
  have hc : 0≤rate m M := div_nonneg (sub_nonneg.mpr hmM) (add_nonneg h.M_pos.le hm.le)
  have hγ0 : 0<γ := hc.trans_lt hγ
  obtain ⟨β,hcβ,hβγ⟩ := exists_between hγ
  obtain ⟨C,hC,hquad⟩ := hilbert_frozen_envelope A hA rule m M β hm hmM hbounds hcβ
  obtain ⟨r,hr,hrR₀,hω⟩ := common_modulus_small_radius ω R₀ hR₀ hlim (m/2) (by positivity)
  obtain ⟨ρ,hρ,hρr,K,hK,henv⟩ := h.uniform_local_envelope rule ω R₀ r hR₀ hr hlim
    β γ C (hc.trans_lt hcβ) hβγ hγ1 hC hquad
  have hK0 : 0<K := zero_lt_one.trans_le hK
  have hCg : 0<M+m/2 := add_pos h.M_pos (div_pos hm (by norm_num))
  have hCF : 0<(M+m/2)/2 := div_pos hCg (by norm_num)
  refine ⟨r,hr,hrR₀,ρ,hρ,hρr,K,hK0,(M+m/2)*K,mul_pos hCg hK0,
    ((M+m/2)/2)*K^2,mul_pos hCF (sq_pos_of_pos hK0),?_⟩
  intro F G hG hmod hgrad
  have hstrict := CommonModulus.hasStrictFDerivAt G A 0 ω R₀ hR₀ hlim hmod
  have hcomparison := h.fixed_ball_comparisons F G hG r hr
    (fun z hz => hgrad z (hz.trans hrR₀)) (by
      intro u hu v hv
      have hh := hmod r ⟨hr,hrR₀⟩ u (by simpa only [sub_zero] using hu)
        v (by simpa only [sub_zero] using hv)
      exact hh.trans (mul_le_mul_of_nonneg_right hω (norm_nonneg _)))
  unfold FixedLocalGuarantee
  simp only [sub_zero]
  refine ⟨?_,?_⟩
  · intro z hz hzne
    have hlow := (hcomparison z hz).2.2.1
    have hpos := mul_pos (div_pos hm (by norm_num : (0:ℝ)<4)) (sq_pos_of_pos (norm_pos_iff.mpr hzne))
    linarith only [hlow,hpos]
  · intro p x hp hx hpx
    obtain ⟨hbound,hdomain,hvalid⟩ := henv G hG hmod p x hp hx (Or.inr hpx)
    have hRinit : 0<max ‖p‖ ‖x‖ := initialRadius_pos p x hpx
    have henvR : ∀ n, ‖bbCurrent rule G p x n‖≤K*γ^n*max ‖p‖ ‖x‖ := by
      intro n
      exact (hbound n).trans (mul_le_mul_of_nonneg_left (le_max_right _ _)
        (mul_nonneg hK0.le (pow_nonneg hγ0.le n)))
    have hlimbound : Tendsto (fun n:ℕ => K*γ^n*‖x‖) atTop (𝓝 0) := by
      simpa only [mul_zero,zero_mul] using
        (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0.le hγ1)).mul_const ‖x‖
    have hconv : Tendsto (bbCurrent rule G p x) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr (squeeze_zero (fun n => norm_nonneg _) hbound hlimbound)
    have hregular : ∀ n, bbCurrent rule G p x n≠0 → bbPrevious rule G p x n≠bbCurrent rule G p x n :=
      fun n hn => Ne.symm (sub_ne_zero.mp (hvalid n hn).1)
    have hroots := nonlinear_convergent_rootFactors rule F G 0 A hA m M R₀ hm hmM hbounds
      hG hstrict hR₀ (by simpa only [sub_zero] using hgrad) p x hconv hregular _ hRinit
    simp only [sub_zero] at hroots
    refine ⟨hdomain,henvR,?_,?_,hvalid,hconv,hroots.2.1,hroots.2.2.1,hroots.2.2.2⟩
    · intro n
      calc
        _ ≤ (M+m/2)*‖bbCurrent rule G p x n‖ := (hcomparison _ (hdomain n)).2.1
        _ ≤ (M+m/2)*(K*γ^n*max ‖p‖ ‖x‖) := mul_le_mul_of_nonneg_left (henvR n) hCg.le
        _ = _ := by ring
    · intro n
      have hfb := (hcomparison _ (hdomain n)).2.2
      refine ⟨(mul_nonneg (div_nonneg hm.le (by norm_num)) (sq_nonneg _)).trans hfb.1,?_⟩
      have hn := henvR n
      have hnn := norm_nonneg (bbCurrent rule G p x n)
      have hsquare : ‖bbCurrent rule G p x n‖^2≤(K*γ^n*max ‖p‖ ‖x‖)^2 := by
        nlinarith only [hn,hnn]
      calc
        _ ≤ ((M+m/2)/2)*‖bbCurrent rule G p x n‖^2 := hfb.2
        _ ≤ ((M+m/2)/2)*(K*γ^n*max ‖p‖ ‖x‖)^2 := mul_le_mul_of_nonneg_left hsquare hCF.le
        _ = _ := by simp only [mul_pow,←pow_mul,Nat.mul_comm]; ring

/-- Translation transports fixed constants without any new numerical choices. -/
theorem fixed_local_guarantee_translate (rule : Rule) (F : E → ℝ) (G : E → E) (a : E)
    (c γ r ρ Ce Cg CF : ℝ)
    (hzero : FixedLocalGuarantee rule (fun z => F (a+z)) (fun z => G (a+z))
      0 c γ r ρ Ce Cg CF) :
    FixedLocalGuarantee rule F G a c γ r ρ Ce Cg CF := by
  let F' : E → ℝ := fun z => F (a+z)
  let G' : E → E := fun z => G (a+z)
  change FixedLocalGuarantee rule F' G' 0 c γ r ρ Ce Cg CF at hzero
  unfold FixedLocalGuarantee at hzero ⊢
  simp only [sub_zero] at hzero
  obtain ⟨hmin,hlocal⟩ := hzero
  refine ⟨?_,?_⟩
  · intro z hz hza
    have hh := hmin (z-a) hz (sub_ne_zero.mpr hza)
    have hz' : a+(z-a)=z := by abel
    simpa only [F',add_zero,hz'] using hh
  · intro p x hp hx hpx
    have hpx' : p-a≠x-a := by
      intro he
      exact hpx (sub_left_inj.mp he)
    obtain ⟨hdomain,he,hg,hF,hvalid,hconv,hre,hrg,hrF⟩ := hlocal (p-a) (x-a) hp hx hpx'
    have hcur : ∀ n, bbCurrent rule G' (p-a) (x-a) n=bbCurrent rule G p x n-a :=
      bbCurrent_center rule G a p x
    have hprev : ∀ n, bbPrevious rule G' (p-a) (x-a) n=bbPrevious rule G p x n-a :=
      bbPrevious_center rule G a p x
    have hstep : ∀ n, bbStep rule G' (p-a) (x-a) n=bbStep rule G p x n :=
      bbStep_center rule G a p x
    have htranslated : ∀ n, a+bbCurrent rule G' (p-a) (x-a) n=bbCurrent rule G p x n := by
      intro n
      rw [hcur]
      abel
    have hgc : ∀ n, G' (bbCurrent rule G' (p-a) (x-a) n)=G (bbCurrent rule G p x n) := by
      intro n
      exact congrArg G (htranslated n)
    have hfc : ∀ n, F' (bbCurrent rule G' (p-a) (x-a) n)=F (bbCurrent rule G p x n) := by
      intro n
      exact congrArg F (htranslated n)
    have hFzero : F' 0=F a := by simp only [F',add_zero]
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simpa only [hcur] using hdomain
    · simpa only [hcur] using he
    · simpa only [hgc] using hg
    · simpa only [hfc,hFzero] using hF
    · intro n hne
      have hn : bbCurrent rule G' (p-a) (x-a) n≠0 := by
        rw [hcur]
        exact sub_ne_zero.mpr hne
      have hh := hvalid n hn
      have hs : bbCurrent rule G' (p-a) (x-a) n-bbPrevious rule G' (p-a) (x-a) n=
          bbCurrent rule G p x n-bbPrevious rule G p x n := by rw [hcur,hprev]; abel
      simpa only [hs,hgc,hstep] using hh
    · have ht : Tendsto (fun n => a+bbCurrent rule G' (p-a) (x-a) n) atTop (𝓝 a) := by
        simpa only [add_zero] using tendsto_const_nhds.add hconv
      simpa only [htranslated] using ht
    · simpa only [hcur] using hre
    · simpa only [hgc] using hrg
    · simpa only [hfc,hFzero] using hrF

/-- The manuscript's literal dependence-only-on-data statement.

The radii r, ρ and all three envelope constants are chosen before every center
and every F,G sharing the given modulus.  The positivity, minimizer, actual
trajectory, convergence and all three sharp root conclusions are simultaneous.
-/
theorem nonlinear_uniform_modulus (rule : Rule) (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (m M γ R₀ : ℝ) (hm : 0<m) (hmM : m≤M)
    (hbounds : ∀ z:E, m*‖z‖^2≤inner (𝕜:=ℝ) z (A z) ∧ inner (𝕜:=ℝ) z (A z)≤M*‖z‖^2)
    (ω : ℝ → ℝ) (hR₀ : 0<R₀) (hlim : Tendsto ω (nhdsWithin 0 (Ioi 0)) (𝓝 0))
    (hγ : rate m M<γ) (hγ1 : γ<1) :
    ∃ r>0, r≤R₀ ∧ ∃ ρ>0, ρ≤r ∧ ∃ Ce>0, ∃ Cg>0, ∃ CF>0,
      ∀ (a:E) (F:E→ℝ) (G:E→E), G a=0 → CommonModulus G A a ω R₀ →
        (∀ z, ‖z-a‖≤R₀ → HasGradientAt F (G z) z) →
        FixedLocalGuarantee rule F G a (rate m M) γ r ρ Ce Cg CF := by
  obtain ⟨r,hr,hrR₀,ρ,hρ,hρr,Ce,hCe,Cg,hCg,CF,hCF,hzero⟩ :=
    nonlinear_uniform_modulus_zero rule A hA m M γ R₀ hm hmM hbounds ω hR₀ hlim hγ hγ1
  refine ⟨r,hr,hrR₀,ρ,hρ,hρr,Ce,hCe,Cg,hCg,CF,hCF,?_⟩
  intro a F G hG hmod hgrad
  apply fixed_local_guarantee_translate rule F G a (rate m M) γ r ρ Ce Cg CF
  apply hzero (fun z => F (a+z)) (fun z => G (a+z))
  · simpa only [add_zero] using hG
  · exact CommonModulus.translate G A a ω R₀ hmod
  · intro z hz
    apply gradient_translate F G a z
    apply hgrad
    simpa only [add_sub_cancel_left] using hz

end BB.Nonlinear
