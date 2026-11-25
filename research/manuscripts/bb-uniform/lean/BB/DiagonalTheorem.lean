import BB.Rescaled
import BB.SignInvariant

/-!
# Exact common rate for every changing diagonal spectral weight

This module proves the finite-spectral induction for the actual quotients
`vectorAlpha`, not for a recurrence with convergence assumed.  The ambient
norm is the coordinate sup norm, and each interval may contain zero active
components.  Its prefactor is uniform over all normalized weights in
`[1, χ]`, all initial pairs in the cone, and all weight words/sequences.
-/

noncomputable section
namespace BB.Diagonal

open BB.Spectral BB.Faces BB.Gluing

variable {n : ℕ}

def AbsCertificate (lam : Fin n → ℝ) (χ M r : ℝ) (lo hi : Fin n) :=
  {v : Certificate (T lam (χ := χ)) (stateSet M lo hi) r //
    ∀ z, v.value (absState z) = v.value z}

theorem certificate_of_boundary {lam : Fin n → ℝ} {a b χ M r : ℝ} {lo hi : Fin n}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM0 : 0 ≤ M) (hr : 0 < r)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (hmono : StrictMono lam) (hlohi : lo < hi)
    (hcr : BB.endpointRate (lam lo) (lam hi) ≤ r)
    {N : ℕ} (hN : 1 < N)
    (hboundary : ∀ l : List (Weights n χ), l.length = N → ∀ z ∈ stateSet M lo hi,
      endpointProduct lam lo hi z = 0 → ‖run (S lam r) l z‖ ≤ (1/2 : ℝ) * ‖z‖) :
    Nonempty (AbsCertificate lam χ M r lo hi) := by
  have hp : 0 < lam lo := ha.trans_le (hlama lo)
  have hlt : lam lo < lam hi := hmono hlohi
  let L := scaledLip n a b χ M r
  have hL : 1 ≤ L := scaledLip_ge_one n a b χ M r
  obtain ⟨v,hv⟩ := finite_horizon_certificate
    hr.le hL hN
    (fun z hz t _ => stateSet_smul hz t)
    (fun w z hz => S_mem ha hab hlama hlamb hM w hz)
    (fun w z _ => T_eq_scale_S lam hr.ne' w z)
    (fun w z hz => S_bound ha hab hχ hM0 hr hlama hlamb w hz.1)
    (fun w x y hx hy => S_lipschitz ha hab hχ hM0 hr hlama hlamb w hx.1 hy.1)
    (fun w z _ t _ => S_smul lam r w z t)
    (fun w z hz => endpointProduct_S hp hmono hlohi hr hcr w hz)
    (fun z _ => endpointProduct_le_norm hp hlt z)
    (fun z _ t ht => endpointProduct_homogeneous hp hlt z ht)
    (fun z hz => endpoint_deletion hp hlt hz)
    hboundary
    (by
      intro A hA
      obtain ⟨J,hJ,hLip⟩ := endpoint_Q_regular hp hlt hA
      exact ⟨J,hJ,fun x y _ _ => hLip x y⟩)
  refine ⟨⟨v, ?_⟩⟩
  intro z
  rw [hv]
  exact endpoint_V_abs lam (fun w : Weights n χ => w.val) lo hi r⁻¹ (2*L^N) N z

theorem certificate_singleton {lam : Fin n → ℝ} {a b χ M r : ℝ} {i : Fin n}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM0 : 0 ≤ M) (hr : 0 < r)
    (hlama : ∀ j, a ≤ lam j) (hlamb : ∀ j, lam j ≤ b) (hM : b/a-1 ≤ M) :
    Nonempty (AbsCertificate lam χ M r i i) := by
  let L := scaledLip n a b χ M r
  have hL : 1 ≤ L := scaledLip_ge_one n a b χ M r
  have hboundary : ∀ l : List (Weights n χ), l.length = 2 → ∀ z ∈ stateSet M i i,
      (fun _ : State (Fin n) => (0 : ℝ)) z = 0 →
      ‖run (S lam r) l z‖ ≤ (1/2 : ℝ) * ‖z‖ := by
    intro l hl z hz _
    cases l with
    | nil => simp at hl
    | cons w l =>
      cases l with
      | nil => simp at hl
      | cons w' l =>
        have hl0 : l = [] := by
          apply List.length_eq_zero.mp
          simp only [List.length_cons] at hl
          omega
        subst l
        have hnil : T lam w' (T lam w z) = 0 :=
          singleton_two_updates (ha.trans_le (hlama i)) (fun j => (w.property j).1) hz
        simp only [run_cons, run_nil, S, T_smul, hnil, smul_zero, norm_zero]
        positivity
  obtain ⟨v,hv⟩ := finite_horizon_certificate
    (P := fun _ => (0 : ℝ)) hr.le hL (by norm_num : 1 < (2 : ℕ))
    (fun z hz t _ => stateSet_smul hz t)
    (fun w z hz => S_mem ha hab hlama hlamb hM w hz)
    (fun w z _ => T_eq_scale_S lam hr.ne' w z)
    (fun w z hz => S_bound ha hab hχ hM0 hr hlama hlamb w hz.1)
    (fun w x y hx hy => S_lipschitz ha hab hχ hM0 hr hlama hlamb w hx.1 hy.1)
    (fun w z _ t _ => S_smul lam r w z t)
    (fun _ _ _ => le_refl 0)
    (fun z _ => norm_nonneg z)
    (by intros; simp)
    (by intro z hz; exact ⟨z,hz,rfl,le_refl _,by simp⟩)
    hboundary
    (by
      intro A hA
      refine ⟨1,by norm_num,?_⟩
      intro x y hx hy
      simpa only [Q, mul_zero, max_eq_left (norm_nonneg _), one_mul] using abs_norm_sub_norm_le x y)
  refine ⟨⟨v, ?_⟩⟩
  intro z
  rw [hv]
  exact finite_horizon_V_abs lam (fun w : Weights n χ => w.val) r⁻¹ (2*L^2)
    2 (fun _ => (0 : ℝ)) (fun _ => rfl) z

/-- Exact critical-rate finite-spectrum theorem in diagonal coordinates.

The strengthened formulation allows any positive rate at least the endpoint
factor.  That includes single-eigenvalue faces without assigning the false
one-step rate `0` to a two-step state. -/
theorem interval_has_certificate {lam : Fin n → ℝ} {a b χ M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM0 : 0 ≤ M)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (hmono : StrictMono lam)
    (lo hi : Fin n) (hlohi : lo ≤ hi) (r : ℝ) (hr : 0 < r)
    (hcr : BB.endpointRate (lam lo) (lam hi) ≤ r) :
    Nonempty (AbsCertificate lam χ M r lo hi) := by
  have allIntervals : ∀ d : ℕ, ∀ lo hi : Fin n, lo ≤ hi → hi.val-lo.val = d →
      ∀ r : ℝ, 0 < r → BB.endpointRate (lam lo) (lam hi) ≤ r →
      Nonempty (AbsCertificate lam χ M r lo hi) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro lo hi hlohi hd r hr hcr
      by_cases heq : lo = hi
      · subst hi
        exact certificate_singleton ha hab hχ hM0 hr hlama hlamb hM
      have hlt : lo < hi := lt_of_le_of_ne hlohi heq
      have hval : lo.val < hi.val := hlt
      let lo' : Fin n := ⟨lo.val+1, by omega⟩
      let hi' : Fin n := ⟨hi.val-1, by omega⟩
      have hlo' : lo'.val = lo.val+1 := rfl
      have hhi' : hi'.val+1 = hi.val := by dsimp [hi']; omega
      have hlolo' : lo < lo' := by change lo.val < lo'.val; omega
      have hhi'hi : hi' < hi := by change hi'.val < hi.val; omega
      have hlo'hi : lo' ≤ hi := by change lo'.val ≤ hi.val; omega
      have hlohi' : lo ≤ hi' := by change lo.val ≤ hi'.val; omega
      have d₁ : hi.val-lo'.val < d := by omega
      have d₂ : hi'.val-lo.val < d := by omega
      let cp := BB.endpointRate (lam lo) (lam hi)
      let c₁ := BB.endpointRate (lam lo') (lam hi)
      let c₂ := BB.endpointRate (lam lo) (lam hi')
      have hp : 0 < lam lo := ha.trans_le (hlama lo)
      have hp' : 0 < lam lo' := ha.trans_le (hlama lo')
      have hcp : 0 < cp := BB.endpointRate_pos hp (hmono hlt)
      have hc₁0 : 0 ≤ c₁ := by
        dsimp [c₁, BB.endpointRate]
        exact div_nonneg (sub_nonneg.mpr (hmono.monotone hlo'hi)) (by linarith [hmono.monotone hlo'hi])
      have hc₂0 : 0 ≤ c₂ := by
        dsimp [c₂, BB.endpointRate]
        exact div_nonneg (sub_nonneg.mpr (hmono.monotone hlohi')) (by linarith [hmono.monotone hlohi'])
      have hc₁ : c₁ < cp := rate_raise_lower hp (hmono hlolo') (hmono.monotone hlo'hi)
      have hc₂ : c₂ < cp := rate_lower_upper hp (hmono.monotone hlohi') (hmono hhi'hi)
      let r₁ := (c₁+cp)/2
      let r₂ := (c₂+cp)/2
      have hr₁ : 0 < r₁ := by dsimp [r₁]; linarith
      have hr₂ : 0 < r₂ := by dsimp [r₂]; linarith
      have hcr₁ : c₁ ≤ r₁ := by dsimp [r₁]; linarith
      have hcr₂ : c₂ ≤ r₂ := by dsimp [r₂]; linarith
      have hr₁r : r₁ < r := by dsimp [r₁]; change cp ≤ r at hcr; linarith
      have hr₂r : r₂ < r := by dsimp [r₂]; change cp ≤ r at hcr; linarith
      obtain ⟨v₁⟩ := ih _ d₁ lo' hi hlo'hi rfl r₁ hr₁ hcr₁
      obtain ⟨v₂⟩ := ih _ d₂ lo hi' hlohi' rfl r₂ hr₂ hcr₂
      let L := scaledLip n a b χ M r
      have hL : 1 ≤ L := scaledLip_ge_one n a b χ M r
      have hhandoff : ∀ (w : Weights n χ) z, z ∈ stateSet M lo hi →
          endpointProduct lam lo hi z = 0 →
          S lam r w z ∈ stateSet M lo' hi ∪ stateSet M lo hi' := by
        intro w z hz hzero
        rcases (endpointProduct_eq_zero_iff hp (hmono hlt) z).mp hzero with hzero | hzero
        · left
          exact stateSet_smul (stateMap_handoff_lower ha hab (fun j => (w.property j).1)
            hlama hlamb hM hlo' hz hzero) r⁻¹
        · right
          exact stateSet_smul (stateMap_handoff_upper ha hab (fun j => (w.property j).1)
            hlama hlamb hM hhi' hz hzero) r⁻¹
      obtain ⟨N,hN,hboundary⟩ := exists_uniform_boundary_length
        hL v₁.val.prefactor_ge_one v₂.val.prefactor_ge_one
        (div_nonneg hr₁.le hr.le) ((div_lt_one hr).mpr hr₁r)
        (div_nonneg hr₂.le hr.le) ((div_lt_one hr).mpr hr₂r)
        (fun w z hz => S_bound ha hab hχ hM0 hr hlama hlamb w hz.1)
        hhandoff
        (fun l z hz => rescaled_word_bound ha hab hr hr₁.le hlama hlamb hM v₁.val l hz)
        (fun l z hz => rescaled_word_bound ha hab hr hr₂.le hlama hlamb hM v₂.val l hz)
      exact certificate_of_boundary ha hab hχ hM0 hr hlama hlamb hM hmono hlt hcr
        (by omega) hboundary
  exact allIntervals (hi.val-lo.val) lo hi hlohi rfl r hr hcr

/-- The exact endpoint factor, with a single constant and a single function
for all admissible weights and all initial states on an interval. -/
theorem exact_interval_rate {lam : Fin n → ℝ} {a b χ M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM0 : 0 ≤ M)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (hmono : StrictMono lam) (lo hi : Fin n) (hlohi : lo < hi) :
    ∃ v : Certificate (T lam (χ := χ)) (stateSet M lo hi)
        (BB.endpointRate (lam lo) (lam hi)), ∀ z, v.value (absState z) = v.value z := by
  have hr := BB.endpointRate_pos (ha.trans_le (hlama lo)) (hmono hlohi)
  obtain ⟨v⟩ := interval_has_certificate ha hab hχ hM0 hlama hlamb hM hmono lo hi hlohi.le _ hr le_rfl
  exact ⟨v.val,v.property⟩

theorem supported_full (u : Fin (n+2) → ℝ) : supported 0 (Fin.last (n+1)) u := by
  intro i hi
  rcases hi with h | h
  · exact False.elim (by change i.val < 0 at h; omega)
  · exact False.elim (by change n+1 < i.val at h; have := i.isLt; omega)

theorem stateSet_full (M : ℝ) :
    stateSet M (0 : Fin (n+2)) (Fin.last (n+1)) = {z | Cone M z} := by
  ext z
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h,supported_full z.1,supported_full z.2⟩

/-- The full diagonal BB theorem, with no support premise on the initial pair. -/
theorem full_exact_rate (lam : Fin (n+2) → ℝ) {χ M : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (hM1 : 1 ≤ M)
    (hM : lam (Fin.last (n+1)) / lam 0 - 1 ≤ M) :
    ∃ v : Certificate (T lam (χ := χ)) {z | Cone M z}
        (BB.endpointRate (lam 0) (lam (Fin.last (n+1)))),
      ∀ z, v.value (absState z) = v.value z := by
  have hlohi : (0 : Fin (n+2)) < Fin.last (n+1) := by change 0 < n+1; omega
  have hmin : ∀ i, lam 0 ≤ lam i := fun i => hmono.monotone (Fin.zero_le i)
  have hmax : ∀ i, lam i ≤ lam (Fin.last (n+1)) := fun i => hmono.monotone (Fin.le_last i)
  have h := exact_interval_rate (χ := χ) (M := M) ha (hmono hlohi).le (by linarith : 0 ≤ χ)
    (by linarith : 0 ≤ M) hmin hmax hM hmono (0 : Fin (n+2)) (Fin.last (n+1)) hlohi
  rw [stateSet_full] at h
  exact h

/-- A single prefactor controls every admissible diagonal trajectory. -/
theorem full_uniform_bound (lam : Fin (n+2) → ℝ) {χ M : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (hM1 : 1 ≤ M)
    (hM : lam (Fin.last (n+1)) / lam 0 - 1 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (w : ℕ → Weights (n+2) χ) (z : ℕ → State (Fin (n+2))),
      Cone M (z 0) → (∀ k, z (k+1) = T lam (w k) (z k)) →
      ∀ k, ‖z k‖ ≤ K * (BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^k * ‖z 0‖ := by
  obtain ⟨v,hv⟩ := full_exact_rate lam hmono ha hχ hM1 hM
  refine ⟨v.prefactor,v.prefactor_ge_one,?_⟩
  intro w z hz hrec k
  have hstates : ∀ j, z j ∈ {z | Cone M z} := by
    intro j
    induction j with
    | zero => exact hz
    | succ j ih =>
      rw [hrec j]
      exact stateMap_cone ha (hmono.monotone (Fin.zero_le _))
        (fun i => ((w j).property i).1)
        (fun i => hmono.monotone (Fin.zero_le i))
        (fun i => hmono.monotone (Fin.le_last i)) hM ih
  have hr : 0 ≤ BB.endpointRate (lam 0) (lam (Fin.last (n+1))) := by
    apply (BB.endpointRate_pos ha (hmono ?_)).le
    change 0 < n+1
    omega
  exact v.trajectory_bound hr z w hstates hrec k

end BB.Diagonal
