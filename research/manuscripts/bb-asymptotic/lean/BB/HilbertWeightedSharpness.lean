import BB.HilbertSharpness
import BB.UniversalWeighted

/-!
# Exact endpoint attainment for weighted Hilbert rules

The weight is an actual linear operator with the stated actions on the two
endpoint eigenspaces. No existence of a Borel functional calculus is assumed
implicitly. The BB2 specialization takes the weight operator to be `A`.
-/

noncomputable section
namespace BB
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

def operatorWeightedBB (A W : E →ₗ[ℝ] E) (x : E) : ℝ :=
  ⟪x,W x⟫ / ⟪x,W (A x)⟫

theorem operator_weighted_bb2 (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) (x : E) :
    operatorWeightedBB A A x = operatorBB2 A x := by
  unfold operatorWeightedBB operatorBB2
  rw [← hA x (A x), real_inner_self_eq_norm_sq]

theorem operator_weighted_two_eigenvectors (A W : E →ₗ[ℝ] E) (a b wa wb : ℝ) (p q : E)
    (hp : A p = a•p) (hq : A q = b•q) (hwp : W p = wa•p) (hwq : W q = wb•q)
    (horth : ⟪p,q⟫ = 0) (u v : ℝ) :
    operatorWeightedBB A W (u•p+v•q) =
      (wa*(u*‖p‖)^2+wb*(v*‖q‖)^2) /
        (a*wa*(u*‖p‖)^2+b*wb*(v*‖q‖)^2) := by
  have hcp : (W.comp A) p = (a*wa)•p := by simp only [LinearMap.comp_apply, hp, map_smul, hwp, smul_smul]
  have hcq : (W.comp A) q = (b*wb)•q := by simp only [LinearMap.comp_apply, hq, map_smul, hwq, smul_smul]
  unfold operatorWeightedBB
  rw [eigen_combination_energy_inner W wa wb p q hwp hwq horth]
  change _ / ⟪u•p+v•q,(W.comp A) (u•p+v•q)⟫ = _
  rw [eigen_combination_energy_inner (W.comp A) (a*wa) (b*wb) p q hcp hcq horth]
  congr 1 <;> ring

lemma weighted_balanced_quotient (a b wa wb x y : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwa : 0 < wa) (hx : x ≠ 0) (hbal : wa*x^2=wb*y^2) :
    (wa*x^2+wb*y^2)/(a*wa*x^2+b*wb*y^2) = 2/(a+b) := by
  have hxw : 0 < wa*x^2 := mul_pos hwa (sq_pos_of_ne_zero hx)
  have hd : a*wa*x^2+b*wb*y^2 = (a+b)*(wa*x^2) := by rw [mul_assoc b wb, ← hbal]; ring
  rw [hd, ← hbal]
  field_simp [(by positivity : a+b ≠ 0), hxw.ne']
  ring

theorem hilbert_weighted_endpoint_orbit_quotient (A W : E →ₗ[ℝ] E)
    (a b wa wb : ℝ) (ha : 0 < a) (hab : a < b) (hwa : 0 < wa) (p q : E)
    (hp : A p = a•p) (hq : A q = b•q) (hwp : W p = wa•p) (hwq : W q = wb•q)
    (horth : ⟪p,q⟫ = 0) (hp0 : p ≠ 0) (hbal : wa*‖p‖^2=wb*‖q‖^2) (k : ℕ) :
    operatorWeightedBB A W (hilbertEndpointOrbit a b p q k) = 2/(a+b) := by
  rw [hilbertEndpointOrbit, operator_weighted_two_eigenvectors A W a b wa wb p q hp hq hwp hwq horth]
  apply weighted_balanced_quotient a b wa wb _ _ ha (ha.trans hab) hwa
  · exact mul_ne_zero (pow_ne_zero k (rate_pos ha hab).ne') (norm_ne_zero_iff.mpr hp0)
  · have hneg : ((-(rate a b))^k)^2 = ((rate a b)^k)^2 := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul, neg_sq,
        ← pow_mul, Nat.mul_comm 2 k, pow_mul]
    rw [mul_pow, mul_pow, hneg]
    nlinarith [congrArg (fun t : ℝ => ((rate a b)^k)^2*t) hbal]

theorem hilbert_weighted_endpoint_matched_orbit (A W : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (a b wa wb : ℝ) (ha : 0 < a) (hab : a < b) (hwa : 0 < wa)
    (p q : E) (hp : A p = a•p) (hq : A q = b•q) (hwp : W p = wa•p) (hwq : W q = wb•q)
    (hp0 : p ≠ 0) (hbal : wa*‖p‖^2=wb*‖q‖^2) :
    let g := hilbertEndpointOrbit a b p q
    g 0 ≠ 0 ∧ 0 < operatorWeightedBB A W (g 0) ∧
      g 1 = operatorGradientStep A (operatorWeightedBB A W (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep A (operatorWeightedBB A W (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖/‖g 0‖) = rate a b := by
  dsimp only
  have horth := distinct_eigenvectors_inner_zero A hA a b hab.ne p q hp hq
  have h0 : hilbertEndpointOrbit a b p q 0 ≠ 0 := by
    intro hz
    have hsq := orthogonal_combination_norm_sq p q horth 1 1
    simp only [one_smul, one_pow, one_mul] at hsq
    have hz' : p+q = 0 := by simpa only [hilbertEndpointOrbit, pow_zero, one_smul] using hz
    rw [hz', norm_zero] at hsq
    nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hp0), sq_nonneg ‖q‖]
  have hquot := hilbert_weighted_endpoint_orbit_quotient A W a b wa wb ha hab hwa p q
    hp hq hwp hwq horth hp0 hbal
  have hnorm := hilbert_endpoint_orbit_norm a b ha hab p q horth
  refine ⟨h0, ?_, ?_, ?_, hnorm, ?_⟩
  · rw [hquot 0]; exact div_pos (by norm_num) (by linarith)
  · rw [hquot 0]; exact (hilbert_endpoint_orbit_step A a b ha hab p q hp hq 0).symm
  · intro n
    rw [hquot n]; exact (hilbert_endpoint_orbit_step A a b ha hab p q hp hq (n+1)).symm
  · have heq : (fun n => ‖hilbertEndpointOrbit a b p q n‖/‖hilbertEndpointOrbit a b p q 0‖) =
        (fun n => (1:ℝ)*(rate a b)^n) := by
      funext n
      rw [hnorm n, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr h0), one_mul]
    rw [heq]
    exact rootFactor_geometric 1 _ zero_lt_one (rate_pos ha hab).le

/-- BB2 attains the endpoint rate with the spectral balance
`a ‖p‖² = b ‖q‖²`, in an arbitrary real inner-product space. -/
theorem hilbert_bb2_endpoint_matched_orbit (A : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (p q : E) (hp : A p = a•p) (hq : A q = b•q)
    (hp0 : p ≠ 0) (hbal : a*‖p‖^2=b*‖q‖^2) :
    let g := hilbertEndpointOrbit a b p q
    g 0 ≠ 0 ∧ 0 < operatorBB2 A (g 0) ∧
      g 1 = operatorGradientStep A (operatorBB2 A (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep A (operatorBB2 A (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖/‖g 0‖) = rate a b := by
  simpa only [operator_weighted_bb2 A hA] using hilbert_weighted_endpoint_matched_orbit
    A A hA a b a b ha hab ha p q hp hq hp hq hp0 hbal

/-- Nonzero common endpoint eigenvectors can always be scaled to the weighted
balance, so the exact attainment assertion has no hidden normalization premise. -/
theorem hilbert_weighted_endpoint_eigenvalues_attain (A W : E →ₗ[ℝ] E)
    (hA : A.IsSymmetric) (a b wa wb : ℝ) (ha : 0 < a) (hab : a < b)
    (hwa : 0 < wa) (hwb : 0 < wb)
    (hep : ∃ p : E, p ≠ 0 ∧ A p = a•p ∧ W p = wa•p)
    (heq : ∃ q : E, q ≠ 0 ∧ A q = b•q ∧ W q = wb•q) :
    ∃ g : ℕ → E, g 0 ≠ 0 ∧ 0 < operatorWeightedBB A W (g 0) ∧
      g 1 = operatorGradientStep A (operatorWeightedBB A W (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep A (operatorWeightedBB A W (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖/‖g 0‖) = rate a b := by
  obtain ⟨p,hp0,hp,hwp⟩ := hep
  obtain ⟨q,hq0,hq,hwq⟩ := heq
  let p' := (Real.sqrt wb/‖p‖)•p
  let q' := (Real.sqrt wa/‖q‖)•q
  have hpn : ‖p'‖ = Real.sqrt wb := by
    dsimp [p']
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.sqrt_pos.mpr hwb) (norm_pos_iff.mpr hp0)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hp0)]
  have hqn : ‖q'‖ = Real.sqrt wa := by
    dsimp [q']
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos (Real.sqrt_pos.mpr hwa) (norm_pos_iff.mpr hq0)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hq0)]
  have hp' : A p' = a•p' := by dsimp [p']; rw [map_smul, hp, smul_smul, smul_smul, mul_comm]
  have hq' : A q' = b•q' := by dsimp [q']; rw [map_smul, hq, smul_smul, smul_smul, mul_comm]
  have hwp' : W p' = wa•p' := by dsimp [p']; rw [map_smul, hwp, smul_smul, smul_smul, mul_comm]
  have hwq' : W q' = wb•q' := by dsimp [q']; rw [map_smul, hwq, smul_smul, smul_smul, mul_comm]
  have hp0' : p' ≠ 0 := norm_pos_iff.mp (by rw [hpn]; exact Real.sqrt_pos.mpr hwb)
  have hbal : wa*‖p'‖^2=wb*‖q'‖^2 := by rw [hpn,hqn,Real.sq_sqrt hwb.le,Real.sq_sqrt hwa.le,mul_comm]
  exact ⟨hilbertEndpointOrbit a b p' q', hilbert_weighted_endpoint_matched_orbit
    A W hA a b wa wb ha hab hwa p' q' hp' hq' hwp' hwq' hp0' hbal⟩

theorem hilbert_bb2_endpoint_eigenvalues_attain (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hep : ∃ p : E, p ≠ 0 ∧ A p = a•p)
    (heq : ∃ q : E, q ≠ 0 ∧ A q = b•q) :
    ∃ g : ℕ → E, g 0 ≠ 0 ∧ 0 < operatorBB2 A (g 0) ∧
      g 1 = operatorGradientStep A (operatorBB2 A (g 0)) (g 0) ∧
      (∀ n, g (n+2) = operatorGradientStep A (operatorBB2 A (g n)) (g (n+1))) ∧
      (∀ n, ‖g n‖ = (rate a b)^n*‖g 0‖) ∧
      rootFactor (fun n => ‖g n‖/‖g 0‖) = rate a b := by
  obtain ⟨p,hp0,hp⟩ := hep
  obtain ⟨q,hq0,hq⟩ := heq
  simpa only [operator_weighted_bb2 A hA] using hilbert_weighted_endpoint_eigenvalues_attain
    A A hA a b a b ha hab ha (ha.trans hab) ⟨p,hp0,hp,hp⟩ ⟨q,hq0,hq,hq⟩

end BB
