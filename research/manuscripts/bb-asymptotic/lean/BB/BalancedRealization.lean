import BB.OperatorSpectrumSupport
import BB.BalancedProbability
import BB.HilbertSharpness

/-!
# When the balanced abstract spectral state is realized by a vector

The actual half-Dirac probability is realized exactly when both endpoints are
eigenvalues. The necessity uses only the constructed scalar moments, through a
degree-two annihilating polynomial and the two spectral projection polynomials.
-/

namespace BB
noncomputable section
open MeasureTheory Set
open scoped Polynomial
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma polynomial_vector_eigen_of_annihilator (A : E →L[ℝ] E) (x : E) (ell : ℝ) (p : ℝ[X])
    (h : polynomialVector A x ((Polynomial.X-Polynomial.C ell)*p) = 0) :
    A (polynomialVector A x p) = ell • polynomialVector A x p := by
  have he : polynomialVector A x ((Polynomial.X-Polynomial.C ell)*p) =
      A (polynomialVector A x p)-ell • polynomialVector A x p := by
    simp only [polynomialVector,map_mul,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,
      ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.algebraMap_apply]
  exact sub_eq_zero.mp (he.symm.trans h)

theorem balanced_spectral_realization_has_eigenvectors (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a < b)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0)
    (hmeasure : operatorSpectralProbability A hA a b hbounds x hx =
      balancedProbability (⟨a,le_rfl,hab.le⟩ : Icc a b) ⟨b,hab.le,le_rfl⟩) :
    ∃ p q : E, p ≠ 0 ∧ q ≠ 0 ∧ A p = a • p ∧ A q = b • q ∧ ‖p‖ = ‖q‖ := by
  let L := operatorMomentState A hA a b hbounds x hx
  have hL : ∀ f : C(Icc a b,ℝ), L.1 f = (f ⟨a,le_rfl,hab.le⟩+f ⟨b,hab.le,le_rfl⟩)/2 := by
    intro f
    rw [← operator_spectral_integral A hA a b hbounds x hx,hmeasure,balanced_probability_integral]
  let r : ℝ[X] := (Polynomial.X-Polynomial.C a)*(Polynomial.X-Polynomial.C b)
  have hr : polynomialVector A x r = 0 := by
    have hn := operator_polynomial_norm_moment A hA a b hbounds x hx r
    rw [hL] at hn
    simp only [r,ContinuousMap.pow_apply,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap,
      ContinuousMap.coe_mk,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,
      sub_self,zero_mul,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero,zero_div] at hn
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
  let pl : ℝ[X] := Polynomial.C b-Polynomial.X
  let pr : ℝ[X] := Polynomial.X-Polynomial.C a
  have hnl : ‖polynomialVector A x pl‖^2 = ‖x‖^2*((b-a)^2/2) := by
    rw [operator_polynomial_norm_moment A hA a b hbounds x hx pl,hL]
    simp only [pl,ContinuousMap.pow_apply,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap,
      ContinuousMap.coe_mk,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self,
      zero_pow (by decide : 2 ≠ 0),add_zero]
  have hnr : ‖polynomialVector A x pr‖^2 = ‖x‖^2*((b-a)^2/2) := by
    rw [operator_polynomial_norm_moment A hA a b hbounds x hx pr,hL]
    simp only [pr,ContinuousMap.pow_apply,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap,
      ContinuousMap.coe_mk,Polynomial.eval_sub,Polynomial.eval_X,Polynomial.eval_C,sub_self,
      zero_pow (by decide : 2 ≠ 0),zero_add]
  have hpos : 0 < ‖x‖^2*((b-a)^2/2) :=
    mul_pos (sq_pos_of_pos (norm_pos_iff.mpr hx))
      (div_pos (sq_pos_of_pos (sub_pos.mpr hab)) (by norm_num))
  have hpl : polynomialVector A x pl ≠ 0 := by
    intro hz
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hnl
    exact hpos.ne' hnl.symm
  have hpr : polynomialVector A x pr ≠ 0 := by
    intro hz
    rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hnr
    exact hpos.ne' hnr.symm
  refine ⟨polynomialVector A x pl,polynomialVector A x pr,hpl,hpr,?_,?_,?_⟩
  · apply polynomial_vector_eigen_of_annihilator
    have he : (Polynomial.X-Polynomial.C a)*pl = -r := by dsimp [pl,r]; ring
    rw [he]
    change (polynomialVectorLinear A x) (-r) = 0
    rw [map_neg]
    change -polynomialVector A x r = 0
    rw [hr,neg_zero]
  · apply polynomial_vector_eigen_of_annihilator
    have he : (Polynomial.X-Polynomial.C b)*pr = r := by dsimp [pr,r]; ring
    rw [he,hr]
  · nlinarith [norm_nonneg (polynomialVector A x pl),norm_nonneg (polynomialVector A x pr)]

lemma balanced_operator_iterate_eigenvector (A : E →L[ℝ] E) (ell : ℝ) (x : E)
    (hx : A x = ell • x) (k : ℕ) : (A : E → E)^[k] x = ell^k • x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,_root_.map_smul,hx,smul_smul,pow_succ]

theorem balanced_eigenvectors_spectral_probability (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a < b)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (p q : E) (hp : A p = a • p) (hq : A q = b • q) (hp0 : p ≠ 0)
    (hbalance : ‖p‖ = ‖q‖) (hx : p+q ≠ 0) :
    operatorSpectralProbability A hA a b hbounds (p+q) hx =
      balancedProbability (⟨a,le_rfl,hab.le⟩ : Icc a b) ⟨b,hab.le,le_rfl⟩ := by
  have horth := distinct_eigenvectors_inner_zero A.toLinearMap hA a b hab.ne p q hp hq
  have horth' : ⟪q,p⟫ = 0 := by rw [real_inner_comm,horth]
  have hden : ‖p+q‖^2 = 2*‖p‖^2 := by
    rw [norm_add_sq_real,horth,← hbalance]
    ring
  apply probability_functional_injective
  rw [operator_spectral_probability_functional]
  apply positive_state_eq_of_moments
  intro k
  rw [operator_moment_state_power,probability_functional_apply,balanced_probability_integral]
  have hiter : (A : E → E)^[k] (p+q) = a^k • p+b^k • q := by
    rw [← ContinuousLinearMap.coe_pow,map_add]
    simp only [ContinuousLinearMap.coe_pow,balanced_operator_iterate_eigenvector A a p hp k,
      balanced_operator_iterate_eigenvector A b q hq k]
  rw [hiter,hden]
  simp only [inner_add_left,inner_add_right,inner_smul_right,horth,horth',mul_zero,add_zero,zero_add,
    real_inner_self_eq_norm_sq,← hbalance,ContinuousMap.pow_apply,intervalCoordinate,ContinuousMap.coe_mk]
  have hn : ‖p‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hp0)).ne'
  field_simp
  ring

/-- The balanced abstract probability is realized by an actual nonzero vector
if and only if both endpoint eigenspaces are nonzero. -/
theorem balanced_probability_realizable_iff_endpoints_eigenvalues (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (hab : a < b)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2) :
    (∃ (x : E) (hx : x ≠ 0), operatorSpectralProbability A hA a b hbounds x hx =
      balancedProbability (⟨a,le_rfl,hab.le⟩ : Icc a b) ⟨b,hab.le,le_rfl⟩) ↔
      (∃ p : E, p ≠ 0 ∧ A p = a • p) ∧ (∃ q : E, q ≠ 0 ∧ A q = b • q) := by
  constructor
  · rintro ⟨x,hx,hm⟩
    obtain ⟨p,q,hp0,hq0,hp,hq,_hbal⟩ :=
      balanced_spectral_realization_has_eigenvectors A hA a b hab hbounds x hx hm
    exact ⟨⟨p,hp0,hp⟩,⟨q,hq0,hq⟩⟩
  · rintro ⟨⟨p₀,hp₀,hp⟩,⟨q₀,hq₀,hq⟩⟩
    let p : E := ‖q₀‖ • p₀
    let q : E := ‖p₀‖ • q₀
    have hp' : A p = a • p := by dsimp [p]; rw [_root_.map_smul,hp,smul_smul,smul_smul,mul_comm]
    have hq' : A q = b • q := by dsimp [q]; rw [_root_.map_smul,hq,smul_smul,smul_smul,mul_comm]
    have hp0 : p ≠ 0 := smul_ne_zero (norm_ne_zero_iff.mpr hq₀) hp₀
    have hbalance : ‖p‖ = ‖q‖ := by
      simp only [p,q,norm_smul,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_comm]
    have horth := distinct_eigenvectors_inner_zero A.toLinearMap hA a b hab.ne p q hp' hq'
    have hx : p+q ≠ 0 := by
      intro hz
      have hn : ‖p+q‖^2 = ‖p‖^2+‖q‖^2 := by rw [norm_add_sq_real,horth]; ring
      rw [hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hn
      nlinarith [sq_pos_of_pos (norm_pos_iff.mpr hp0),sq_nonneg ‖q‖]
    exact ⟨p+q,hx,balanced_eigenvectors_spectral_probability A hA a b hab hbounds
      p q hp' hq' hp0 hbalance hx⟩

end
end BB
