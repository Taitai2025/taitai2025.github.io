import BB.HilbertSharpness
import BB.ApproxEigen
import BB.HilbertRates

/-!
# Finite-horizon shadowing by approximate endpoint eigenvectors

The vectors used here need not converge and the endpoints need not be
 eigenvalues.  Only the unit norms and the vanishing spectral residuals enter
 the argument.  All trajectories below are the actual matched delayed BB1
 iteration for one fixed bounded selfadjoint operator.
-/

noncomputable section
namespace BB
open Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
local notation "⟪" x ", " y "⟫" => @inner ℝ E _ x y

lemma norm_limit_of_error_zero (x y : ℕ → E) (r : ℝ)
    (he : Tendsto (fun j => x j-y j) atTop (𝓝 0))
    (hy : Tendsto (fun j => ‖y j‖) atTop (𝓝 r)) :
    Tendsto (fun j => ‖x j‖) atTop (𝓝 r) := by
  have hsub : Tendsto (fun j => ‖x j‖-‖y j‖) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_)
      (by simpa using he.norm : Tendsto (fun j => ‖x j-y j‖) atTop (𝓝 0))
    simpa only [Real.norm_eq_abs] using abs_norm_sub_norm_le (x j) (y j)
  simpa only [sub_add_cancel, zero_add] using hsub.add hy

lemma inner_limit_zero_of_norm_product (x y : ℕ → E)
    (h : Tendsto (fun j => ‖x j‖*‖y j‖) atTop (𝓝 0)) :
    Tendsto (fun j => ⟪x j,y j⟫) atTop (𝓝 0) :=
  squeeze_zero_norm (fun j => norm_inner_le_norm (x j) (y j)) h

lemma inner_limit_zero_left (x y : ℕ → E) (r : ℝ)
    (hx : Tendsto x atTop (𝓝 0)) (hy : Tendsto (fun j => ‖y j‖) atTop (𝓝 r)) :
    Tendsto (fun j => ⟪x j,y j⟫) atTop (𝓝 0) := by
  apply inner_limit_zero_of_norm_product
  simpa only [norm_zero, zero_mul] using hx.norm.mul hy

lemma inner_limit_zero_right (x y : ℕ → E) (r : ℝ)
    (hx : Tendsto (fun j => ‖x j‖) atTop (𝓝 r)) (hy : Tendsto y atTop (𝓝 0)) :
    Tendsto (fun j => ⟪x j,y j⟫) atTop (𝓝 0) := by
  apply inner_limit_zero_of_norm_product
  simpa only [norm_zero, mul_zero] using hx.mul hy.norm

lemma inner_continuous_apply_error_zero (A : E →L[ℝ] E) (x y : ℕ → E) (r : ℝ)
    (he : Tendsto (fun j => x j-y j) atTop (𝓝 0))
    (hy : Tendsto (fun j => ‖y j‖) atTop (𝓝 r)) :
    Tendsto (fun j => ⟪x j,A (x j)⟫-⟪y j,A (y j)⟫) atTop (𝓝 0) := by
  have heA : Tendsto (fun j => A (x j-y j)) atTop (𝓝 0) := by
    simpa only [map_zero] using A.continuous.continuousAt.tendsto.comp he
  have hx := norm_limit_of_error_zero x y r he hy
  have hleft : Tendsto (fun j => ⟪x j-y j,A (x j)⟫) atTop (𝓝 0) := by
    apply inner_limit_zero_of_norm_product
    apply squeeze_zero (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (A.le_opNorm (x j)) (norm_nonneg _))
    simpa only [norm_zero, zero_mul] using he.norm.mul (tendsto_const_nhds.mul hx)
  have hright := inner_limit_zero_right y (fun j => A (x j-y j)) r hy heA
  have heq (j : ℕ) : ⟪x j,A (x j)⟫-⟪y j,A (y j)⟫ =
      ⟪x j-y j,A (x j)⟫+⟪y j,A (x j-y j)⟫ := by
    rw [map_sub, inner_sub_left, inner_sub_right]; ring
  simpa only [← heq, zero_add] using hleft.add hright

lemma approximate_eigenvectors_inner_zero (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a ≠ b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) :
    Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0) := by
  have hleft := inner_limit_zero_right p (fun j => A (q j)-b•q j) 1
    (by simpa only [hp] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1))) heq
  have hright := inner_limit_zero_left (fun j => A (p j)-a•p j) q 1 hep
    (by simpa only [hq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1)))
  have he (j : ℕ) : ⟪p j,q j⟫ =
      (⟪p j,A (q j)-b•q j⟫-⟪A (p j)-a•p j,q j⟫)/(a-b) := by
    apply (eq_div_iff (sub_ne_zero.mpr hab)).mpr
    simp only [inner_sub_right, inner_sub_left, inner_smul_right, real_inner_smul_left]
    have hs := hA (p j) (q j)
    change ⟪A (p j),q j⟫ = ⟪p j,A (q j)⟫ at hs
    rw [hs]; ring
  simpa only [← he, sub_zero, zero_div] using (hleft.sub hright).div_const (a-b)

lemma approximate_combination_norm_limit (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hpq : Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0)) (u v : ℝ) :
    Tendsto (fun j => ‖u•p j+v•q j‖) atTop (𝓝 (Real.sqrt (u^2+v^2))) := by
  have hs (j : ℕ) : ‖u•p j+v•q j‖^2 = u^2+v^2+(2*u*v)*⟪p j,q j⟫ := by
    simp only [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      hp, hq, one_pow, mul_one, real_inner_smul_left, inner_smul_right]
    ring
  have ht : Tendsto (fun j => ‖u•p j+v•q j‖^2) atTop (𝓝 (u^2+v^2)) := by
    simpa only [hs, mul_zero, add_zero] using
      (tendsto_const_nhds.add (hpq.const_mul (2*u*v)))
  simpa only [Real.sqrt_sq (norm_nonneg _)] using ht.sqrt

lemma approximate_combination_energy_limit (A : E →L[ℝ] E) (a b : ℝ) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0))
    (hpq : Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0)) (u v : ℝ) :
    Tendsto (fun j => ⟪u•p j+v•q j,A (u•p j+v•q j)⟫) atTop (𝓝 (a*u^2+b*v^2)) := by
  have hn := approximate_combination_norm_limit p q hp hq hpq u v
  have herr : Tendsto (fun j => A (u•p j+v•q j) - ((a*u)•p j+(b*v)•q j)) atTop (𝓝 0) := by
    have he (j : ℕ) : A (u•p j+v•q j) - ((a*u)•p j+(b*v)•q j) =
        u•(A (p j)-a•p j)+v•(A (q j)-b•q j) := by
      simp only [map_add, map_smul, smul_sub, smul_smul]
      rw [mul_comm u a, mul_comm v b]; abel
    simpa only [he, smul_zero, zero_add] using (hep.const_smul u).add (heq.const_smul v)
  have heInner := inner_limit_zero_right (fun j => u•p j+v•q j)
    (fun j => A (u•p j+v•q j) - ((a*u)•p j+(b*v)•q j)) (Real.sqrt (u^2+v^2)) hn herr
  have hsq (j : ℕ) : ⟪u•p j+v•q j,(a*u)•p j+(b*v)•q j⟫ =
      a*u^2+b*v^2+(a+b)*u*v*⟪p j,q j⟫ := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, inner_smul_right,
      real_inner_self_eq_norm_sq, hp, hq, one_pow, mul_one]
    rw [real_inner_comm (p j) (q j)]; ring
  have hmain : Tendsto (fun j => ⟪u•p j+v•q j,(a*u)•p j+(b*v)•q j⟫) atTop (𝓝 (a*u^2+b*v^2)) := by
    simpa only [hsq, mul_zero, add_zero] using
      (tendsto_const_nhds.add (hpq.const_mul ((a+b)*u*v)))
  have hadd := heInner.add hmain
  simpa only [inner_sub_right, sub_add_cancel, zero_add] using hadd

lemma operator_step_error_zero (A : E →L[ℝ] E) (x y : ℕ → E) (r α : ℝ) (αs : ℕ → ℝ)
    (he : Tendsto (fun j => x j-y j) atTop (𝓝 0))
    (hy : Tendsto (fun j => ‖y j‖) atTop (𝓝 r))
    (hα : Tendsto αs atTop (𝓝 α)) :
    Tendsto (fun j => operatorGradientStep A.toLinearMap (αs j) (x j) -
      operatorGradientStep A.toLinearMap α (y j)) atTop (𝓝 0) := by
  have heA : Tendsto (fun j => A (x j-y j)) atTop (𝓝 0) := by
    simpa only [map_zero] using A.continuous.continuousAt.tendsto.comp he
  have hfirst : Tendsto (fun j => x j-y j-αs j•A (x j-y j)) atTop (𝓝 0) := by
    simpa only [smul_zero, sub_zero] using he.sub (hα.smul heA)
  have hlast : Tendsto (fun j => (αs j-α)•A (y j)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_)
      (show Tendsto (fun j => |αs j-α| * (‖A‖*‖y j‖)) atTop (𝓝 0) from by
        simpa only [sub_self, norm_zero, zero_mul, Real.norm_eq_abs] using
          (hα.sub_const α).norm.mul (tendsto_const_nhds.mul hy))
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (A.le_opNorm (y j)) (abs_nonneg _)
  have heq (j : ℕ) : operatorGradientStep A.toLinearMap (αs j) (x j) -
      operatorGradientStep A.toLinearMap α (y j) =
      (x j-y j-αs j•A (x j-y j)) - (αs j-α)•A (y j) := by
    simp only [operatorGradientStep, ContinuousLinearMap.coe_coe, map_sub, smul_sub, sub_smul]
    abel
  simpa only [heq, sub_zero] using hfirst.sub hlast

lemma operator_step_approximate_eigenvectors_identity (A : E →L[ℝ] E)
    (a b α u v : ℝ) (p q : E) :
    operatorGradientStep A.toLinearMap α (u•p+v•q) -
      (((1-α*a)*u)•p+((1-α*b)*v)•q) =
      -α•(u•(A p-a•p)+v•(A q-b•q)) := by
  have hleft : (1-α*a)*u = u-α*(u*a) := by ring
  have hright : (1-α*b)*v = v-α*(v*b) := by ring
  rw [hleft, hright]
  simp only [operatorGradientStep, ContinuousLinearMap.coe_coe, map_add, map_smul,
    smul_add, smul_sub, sub_smul, neg_smul, smul_smul, neg_mul, mul_neg, neg_neg]
  abel

lemma approximate_endpoint_reference_step (A : E →L[ℝ] E) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => operatorGradientStep A.toLinearMap (2/(a+b))
      (hilbertEndpointOrbit a b (p j) (q j) k) -
      hilbertEndpointOrbit a b (p j) (q j) (k+1)) atTop (𝓝 0) := by
  have hs : a+b ≠ 0 := ne_of_gt (by linarith : 0 < a+b)
  have he (j : ℕ) : operatorGradientStep A.toLinearMap (2/(a+b))
      (hilbertEndpointOrbit a b (p j) (q j) k) -
      hilbertEndpointOrbit a b (p j) (q j) (k+1) =
      -(2/(a+b))•((rate a b)^k•(A (p j)-a•p j)+
        (-(rate a b))^k•(A (q j)-b•q j)) := by
    have hid := operator_step_approximate_eigenvectors_identity A a b (2/(a+b))
      ((rate a b)^k) ((-(rate a b))^k) (p j) (q j)
    rw [endpoint_left_multiplier hs, endpoint_right_multiplier hs] at hid
    simpa only [hilbertEndpointOrbit, pow_succ, mul_comm (rate a b), mul_comm (-(rate a b))] using hid
  simpa only [he, smul_zero, zero_add] using
    ((hep.const_smul ((rate a b)^k)).add (heq.const_smul ((-(rate a b))^k))).const_smul (-(2/(a+b)))

lemma approximate_combination_quotient_limit (A : E →L[ℝ] E) (a b : ℝ) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0))
    (hpq : Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0)) (u v : ℝ)
    (hD : a*u^2+b*v^2 ≠ 0) (x : ℕ → E)
    (hx : Tendsto (fun j => x j-(u•p j+v•q j)) atTop (𝓝 0)) :
    Tendsto (fun j => operatorBB1 A.toLinearMap (x j)) atTop
      (𝓝 (bb1Two a b u v)) := by
  have hn := approximate_combination_norm_limit p q hp hq hpq u v
  have hnx := norm_limit_of_error_zero x (fun j => u•p j+v•q j) _ hx hn
  have he := approximate_combination_energy_limit A a b p q hp hq hep heq hpq u v
  have hex := inner_continuous_apply_error_zero A x (fun j => u•p j+v•q j) _ hx hn
  have hDx : Tendsto (fun j => ⟪x j,A (x j)⟫) atTop (𝓝 (a*u^2+b*v^2)) := by
    simpa only [sub_add_cancel, zero_add] using hex.add he
  have hnum : Tendsto (fun j => ‖x j‖^2) atTop (𝓝 (u^2+v^2)) := by
    simpa only [Real.sq_sqrt (add_nonneg (sq_nonneg u) (sq_nonneg v))] using hnx.pow 2
  exact hnum.div hDx hD

lemma approximate_endpoint_quotient_limit (A : E →L[ℝ] E) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0))
    (hpq : Tendsto (fun j => ⟪p j,q j⟫) atTop (𝓝 0)) (k : ℕ) (x : ℕ → E)
    (hx : Tendsto (fun j => x j-hilbertEndpointOrbit a b (p j) (q j) k) atTop (𝓝 0)) :
    Tendsto (fun j => operatorBB1 A.toLinearMap (x j)) atTop (𝓝 (2/(a+b))) := by
  have hcp : 0 < (rate a b)^k := pow_pos (rate_pos ha hab) _
  have hbal : ((rate a b)^k)^2 = ((-(rate a b))^k)^2 := by
    simpa only [mul_one] using endpoint_balance_orbit (rate a b) 1 1 (by rfl) k
  have hD : a*((rate a b)^k)^2+b*((-(rate a b))^k)^2 ≠ 0 := by
    rw [← hbal]
    exact ne_of_gt (by nlinarith [sq_pos_of_pos hcp])
  have hbb := balanced_bb1_step hcp.ne' hbal (a := a) (b := b)
  simpa only [hbb] using approximate_combination_quotient_limit A a b p q hp hq hep heq hpq
    ((rate a b)^k) ((-(rate a b))^k) hD x hx

/-- A total recursive definition, including zero gradients.  The previous and
current gradients are equal only at the initial state. -/
def matchedOperatorPair (A : E →L[ℝ] E) (x : E) : ℕ → E × E
  | 0 => (x,x)
  | n+1 => let z := matchedOperatorPair A x n
      (z.2,operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z.1) z.2)

def matchedOperatorOrbit (A : E →L[ℝ] E) (x : E) (n : ℕ) : E :=
  (matchedOperatorPair A x n).2

@[simp] theorem matchedOperatorOrbit_zero (A : E →L[ℝ] E) (x : E) :
    matchedOperatorOrbit A x 0 = x := rfl

@[simp] theorem matchedOperatorOrbit_one (A : E →L[ℝ] E) (x : E) :
    matchedOperatorOrbit A x 1 = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap x) x := rfl

theorem matchedOperatorOrbit_update (A : E →L[ℝ] E) (x : E) (n : ℕ) :
    matchedOperatorOrbit A x (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (matchedOperatorOrbit A x n)) (matchedOperatorOrbit A x (n+1)) := rfl

theorem approximate_endpoint_matched_pair (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => (matchedOperatorPair A (p j+q j) k).1 -
      hilbertEndpointOrbit a b (p j) (q j) (k-1)) atTop (𝓝 0) ∧
    Tendsto (fun j => (matchedOperatorPair A (p j+q j) k).2 -
      hilbertEndpointOrbit a b (p j) (q j) k) atTop (𝓝 0) := by
  have hpq := approximate_eigenvectors_inner_zero A hA a b hab.ne p q hp hq hep heq
  induction k with
  | zero => simp only [matchedOperatorPair, hilbertEndpointOrbit, pow_zero, one_smul,
      Nat.zero_sub, sub_self]; exact ⟨tendsto_const_nhds,tendsto_const_nhds⟩
  | succ k ih =>
    refine ⟨?_,?_⟩
    · simpa only [matchedOperatorPair, Nat.add_sub_cancel] using ih.2
    · have hα := approximate_endpoint_quotient_limit A a b ha hab p q hp hq hep heq hpq
        (k-1) (fun j => (matchedOperatorPair A (p j+q j) k).1) ih.1
      have hn := approximate_combination_norm_limit p q hp hq hpq ((rate a b)^k) ((-(rate a b))^k)
      have hstep := operator_step_error_zero A
        (fun j => (matchedOperatorPair A (p j+q j) k).2)
        (fun j => hilbertEndpointOrbit a b (p j) (q j) k) _ (2/(a+b))
        (fun j => operatorBB1 A.toLinearMap (matchedOperatorPair A (p j+q j) k).1)
        ih.2 hn hα
      have href := approximate_endpoint_reference_step A a b ha hab p q hep heq k
      simpa only [matchedOperatorPair, sub_add_sub_cancel, zero_add] using hstep.add href

theorem approximate_endpoint_matched_norm_limit (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => ‖matchedOperatorOrbit A (p j+q j) k‖) atTop
      (𝓝 ((rate a b)^k*Real.sqrt 2)) := by
  have hpq := approximate_eigenvectors_inner_zero A hA a b hab.ne p q hp hq hep heq
  have hn := approximate_combination_norm_limit p q hp hq hpq ((rate a b)^k) ((-(rate a b))^k)
  have hval : Real.sqrt (((rate a b)^k)^2+((-(rate a b))^k)^2) = (rate a b)^k*Real.sqrt 2 := by
    simpa only [normTwo, mul_one, one_pow, one_add_one_eq_two] using
      endpoint_norm_orbit (rate_pos ha hab).le 1 1 k
  rw [hval] at hn
  exact norm_limit_of_error_zero _ _ _
    (approximate_endpoint_matched_pair A hA a b ha hab p q hp hq hep heq k).2 hn

theorem approximate_endpoint_matched_ratio_limit (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (k : ℕ) :
    Tendsto (fun j => ‖matchedOperatorOrbit A (p j+q j) k‖/‖p j+q j‖) atTop
      (𝓝 ((rate a b)^k)) := by
  have hn := approximate_endpoint_matched_norm_limit A hA a b ha hab p q hp hq hep heq k
  have h0 := approximate_endpoint_matched_norm_limit A hA a b ha hab p q hp hq hep heq 0
  have hs : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  simpa only [matchedOperatorOrbit_zero, pow_zero, one_mul, mul_div_cancel_right₀ _ hs] using
    hn.div (by simpa only [matchedOperatorOrbit_zero, pow_zero, one_mul] using h0) hs

/-- Any uniform matched-start envelope for one fixed operator has rate at least
its two approximate endpoint values. The prefactor is independent of the start. -/
theorem approximate_endpoints_uniform_rate_ge (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b) (p q : ℕ → E)
    (hp : ∀ j, ‖p j‖ = 1) (hq : ∀ j, ‖q j‖ = 1)
    (hep : Tendsto (fun j => A (p j)-a•p j) atTop (𝓝 0))
    (heq : Tendsto (fun j => A (q j)-b•q j) atTop (𝓝 0)) (C γ : ℝ)
    (hC : 0 < C) (hγ : 0 ≤ γ)
    (henv : ∀ x : E, x ≠ 0 → ∀ k, ‖matchedOperatorOrbit A x k‖ ≤ C*γ^k*‖x‖) :
    rate a b ≤ γ := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have h0 : Tendsto (fun j => ‖p j+q j‖) atTop (𝓝 (Real.sqrt 2)) := by
    simpa only [matchedOperatorOrbit_zero, pow_zero, one_mul] using
      approximate_endpoint_matched_norm_limit A hA a b ha hab p q hp hq hep heq 0
  have hpos : ∀ᶠ j in atTop, 0 < ‖p j+q j‖ := h0.eventually (eventually_gt_nhds hs)
  have hpow : ∀ k : ℕ, (rate a b)^k ≤ C*γ^k := by
    intro k
    apply le_of_tendsto (approximate_endpoint_matched_ratio_limit A hA a b ha hab p q hp hq hep heq k)
    filter_upwards [hpos] with j hj
    exact (div_le_iff hj).mpr (henv (p j+q j) (norm_pos_iff.mp hj) k)
  have hroot := rootFactor_le_of_envelope (fun k => (rate a b)^k)
    (fun k => pow_nonneg (rate_pos ha hab).le k) γ hγ ⟨C,hC,hpow⟩
  have hval : rootFactor (fun k => (rate a b)^k) = rate a b := by
    simpa only [one_mul] using rootFactor_geometric 1 (rate a b) zero_lt_one (rate_pos ha hab).le
  rwa [hval] at hroot

/-- Genuine real spectral endpoints rule out every smaller uniform rate,
including when neither endpoint is an eigenvalue. -/
theorem hilbert_spectral_uniform_rate_ge [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A)
    (C γ : ℝ) (hC : 0 < C) (hγ : 0 ≤ γ)
    (henv : ∀ x : E, x ≠ 0 → ∀ k, ‖matchedOperatorOrbit A x k‖ ≤ C*γ^k*‖x‖) :
    rate a b ≤ γ := by
  obtain ⟨p,q,hpq,hep,heq⟩ := spectrum_approximate_endpoint_sequences A hA a b hab.le hbounds haspec hbspec
  exact approximate_endpoints_uniform_rate_ge A hA a b ha hab p q (fun j => (hpq j).1)
    (fun j => (hpq j).2) (tendsto_zero_iff_norm_tendsto_zero.mpr hep)
    (tendsto_zero_iff_norm_tendsto_zero.mpr heq) C γ hC hγ henv

theorem hilbert_no_smaller_uniform_rate [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < rate a b) :
    ¬ ∃ C : ℝ, 0 < C ∧ ∀ x : E, x ≠ 0 → ∀ k,
      ‖matchedOperatorOrbit A x k‖ ≤ C*γ^k*‖x‖ := by
  rintro ⟨C,hC,henv⟩
  exact (not_le_of_gt hγ) (hilbert_spectral_uniform_rate_ge A hA a b ha hab hbounds
    haspec hbspec C γ hC hγ0 henv)

/-- Positive rates admitting one prefactor for all matched initial gradients of
this fixed operator. -/
def MatchedOperatorUniformRates (A : E →L[ℝ] E) : Set ℝ :=
  {γ | 0 < γ ∧ ∃ C : ℝ, 0 < C ∧ ∀ x : E, x ≠ 0 → ∀ k,
    ‖matchedOperatorOrbit A x k‖ ≤ C*γ^k*‖x‖}

/-- The optimal uniform rate is the exact greatest lower bound of the admissible
rates. Actual real spectrum membership, rather than endpoint eigenvectors,
provides the lower bound. Scalar operators are included. -/
theorem hilbert_matched_uniform_rates_isGLB [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
      inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)
    (haspec : a ∈ spectrum ℝ A) (hbspec : b ∈ spectrum ℝ A) :
    IsGLB (MatchedOperatorUniformRates A) (rate a b) := by
  have hc : 0 ≤ rate a b := div_nonneg (sub_nonneg.mpr hab) (by linarith)
  have hupper : ∀ γ : ℝ, rate a b < γ → γ ∈ MatchedOperatorUniformRates A := by
    intro γ hγ
    obtain ⟨C,hC,henv⟩ := hilbert_matched_uniform_envelope A hA a b γ ha hab hbounds hγ
    refine ⟨hc.trans_lt hγ,C,hC,?_⟩
    intro x hx k
    exact henv (matchedOperatorOrbit A x) hx (matchedOperatorOrbit_one A x)
      (matchedOperatorOrbit_update A x) k
  constructor
  · intro γ hγ
    rcases hγ with ⟨hγpos,C,hC,henv⟩
    rcases hab.lt_or_eq with hablt | habeq
    · exact hilbert_spectral_uniform_rate_ge A hA a b ha hablt hbounds haspec hbspec
        C γ hC hγpos.le henv
    · subst b
      simpa only [rate, sub_self, zero_div] using hγpos.le
  · intro d hd
    apply le_of_forall_strict_upper_bound
    intro γ hγ
    exact hd (hupper γ hγ)

end BB
