import BB.OperatorPolynomial
import BB.ApproxEigen
import Mathlib.Topology.Sequences

/-!
# Actual commuting square roots on real Hilbert spaces

Polynomial norm bounds follow from the proved scalar moment construction.
Weierstrass approximation and completeness then construct an actual bounded
operator square root. No continuous or Borel operator calculus is assumed.
-/

noncomputable section
namespace BB
open Set Filter
open scoped Polynomial Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem polynomial_operator_norm_le (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (p : ℝ[X]) : ‖Polynomial.aeval A p‖ ≤ ‖p.toContinuousMapOn (Icc a b)‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  by_cases hx : x = 0
  · simp [hx]
  let L := operatorMomentState A hA a b hbounds x hx
  let f := p.toContinuousMapOn (Icc a b)
  have htest : L.1 (f^2) ≤ ‖f‖^2 := by
    have h := positive_unit_mono L.2 (f := f^2)
      (g := ContinuousMap.const (Icc a b) (‖f‖^2)) (fun t => ?_)
    · simpa only [positive_unit_const L.2] using h
    · change (f t)^2 ≤ ‖f‖^2
      have hn := f.norm_coe_le_norm t
      rw [Real.norm_eq_abs] at hn
      nlinarith [sq_abs (f t), abs_nonneg (f t), norm_nonneg f]
  have he := operator_polynomial_norm_moment A hA a b hbounds x hx p
  have hsq := mul_le_mul_of_nonneg_left htest (sq_nonneg ‖x‖)
  change ‖(Polynomial.aeval A p) x‖^2 = ‖x‖^2 * L.1 (f^2) at he
  have hn2 := mul_nonneg (norm_nonneg f) (norm_nonneg x)
  change ‖(Polynomial.aeval A p) x‖ ≤ ‖f‖ * ‖x‖
  nlinarith

theorem continuous_polynomial_sequence (a b : ℝ) (f : C(Icc a b, ℝ)) :
    ∃ p : ℕ → ℝ[X], Tendsto (fun n => (p n).toContinuousMapOn (Icc a b)) atTop (𝓝 f) := by
  obtain ⟨fs, hfs, hlim⟩ := mem_closure_iff_seq_limit.mp
    (continuousMap_mem_polynomialFunctions_closure a b f)
  have he : ∀ n, ∃ p : ℝ[X], p.toContinuousMapOn (Icc a b) = fs n := by
    intro n
    have h := hfs n
    rw [polynomialFunctions_coe] at h
    exact h
  choose p hp using he
  exact ⟨p, by simpa only [hp] using hlim⟩

theorem polynomial_square_operator_error (W : E →L[ℝ] E)
    (hW : W.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,W x⟫ ∧ ⟪x,W x⟫ ≤ b*‖x‖^2)
    (p : ℝ[X]) :
    ‖Polynomial.aeval W p * Polynomial.aeval W p - W‖ ≤
      ‖(p*p-Polynomial.X).toContinuousMapOn (Icc a b)‖ := by
  have h := polynomial_operator_norm_le W hW a b hbounds (p*p-Polynomial.X)
  rw [map_sub, map_mul, Polynomial.aeval_X] at h
  exact h

theorem polynomial_operator_sequence_cauchy (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (p : ℕ → ℝ[X]) (hc : CauchySeq (fun n => (p n).toContinuousMapOn (Icc a b))) :
    CauchySeq (fun n => Polynomial.aeval A (p n)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hc ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  apply lt_of_le_of_lt _ (hN m hm n hn)
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  have he : (p m - p n).toContinuousMapOn (Icc a b) =
      (p m).toContinuousMapOn (Icc a b) - (p n).toContinuousMapOn (Icc a b) := by ext t; simp
  simpa only [he] using polynomial_operator_norm_le A hA a b hbounds (p m - p n)

theorem operator_polynomial_limit_exists [CompleteSpace E] (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (f : C(Icc a b, ℝ)) :
    ∃ (p : ℕ → ℝ[X]) (S : E →L[ℝ] E),
      Tendsto (fun n => (p n).toContinuousMapOn (Icc a b)) atTop (𝓝 f) ∧
      Tendsto (fun n => Polynomial.aeval A (p n)) atTop (𝓝 S) := by
  obtain ⟨p,hp⟩ := continuous_polynomial_sequence a b f
  obtain ⟨S,hS⟩ := cauchySeq_tendsto_of_complete
    (polynomial_operator_sequence_cauchy A hA a b hbounds p hp.cauchySeq)
  exact ⟨p,S,hp,hS⟩

theorem operator_limit_apply {p : ℕ → E →L[ℝ] E} {S : E →L[ℝ] E}
    (hS : Tendsto p atTop (𝓝 S)) (x : E) :
    Tendsto (fun n => p n x) atTop (𝓝 (S x)) :=
  ((ContinuousLinearMap.apply ℝ E x).continuous.tendsto S).comp hS

theorem operator_polynomial_limit_symmetric (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (p : ℕ → ℝ[X]) (S : E →L[ℝ] E)
    (hS : Tendsto (fun n => Polynomial.aeval A (p n)) atTop (𝓝 S)) :
    S.toLinearMap.IsSymmetric := by
  intro x y
  have hleft : Tendsto (fun n => ⟪(Polynomial.aeval A (p n)) x,y⟫) atTop (𝓝 ⟪S x,y⟫) :=
    (operator_limit_apply hS x).inner tendsto_const_nhds
  have hright : Tendsto (fun n => ⟪x,(Polynomial.aeval A (p n)) y⟫) atTop (𝓝 ⟪x,S y⟫) :=
    tendsto_const_nhds.inner (operator_limit_apply hS y)
  have he : (fun n => ⟪(Polynomial.aeval A (p n)) x,y⟫) =
      (fun n => ⟪x,(Polynomial.aeval A (p n)) y⟫) :=
    funext (fun n => operator_polynomial_symmetric A hA (p n) x y)
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem operator_polynomial_limit_form (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)
    (f : C(Icc a b, ℝ)) (p : ℕ → ℝ[X]) (S : E →L[ℝ] E)
    (hp : Tendsto (fun n => (p n).toContinuousMapOn (Icc a b)) atTop (𝓝 f))
    (hS : Tendsto (fun n => Polynomial.aeval A (p n)) atTop (𝓝 S))
    (x : E) (hx : x ≠ 0) :
    ⟪x,S x⟫ = ‖x‖^2 * (operatorMomentState A hA a b hbounds x hx).1 f := by
  let L := operatorMomentState A hA a b hbounds x hx
  have hleft : Tendsto (fun n => ⟪x,(Polynomial.aeval A (p n)) x⟫) atTop (𝓝 ⟪x,S x⟫) :=
    tendsto_const_nhds.inner (operator_limit_apply hS x)
  have hright : Tendsto (fun n => ‖x‖^2 * L.1 ((p n).toContinuousMapOn (Icc a b)))
      atTop (𝓝 (‖x‖^2 * L.1 f)) :=
    tendsto_const_nhds.mul (((WeakDual.toNormedDual L.1).continuous.tendsto f).comp hp)
  have he : (fun n => ⟪x,(Polynomial.aeval A (p n)) x⟫) =
      (fun n => ‖x‖^2 * L.1 ((p n).toContinuousMapOn (Icc a b))) := by
    funext n
    rw [operator_moment_state_polynomial]
    have hn : ‖x‖^2 ≠ 0 := (sq_pos_of_pos (norm_pos_iff.mpr hx)).ne'
    change ⟪x,(Polynomial.aeval A (p n)) x⟫ = ‖x‖^2 * (⟪x,(Polynomial.aeval A (p n)) x⟫ / ‖x‖^2)
    field_simp
  rw [he] at hleft
  exact tendsto_nhds_unique hleft hright

theorem operator_iterate_commutes (A W : E →L[ℝ] E)
    (hcomm : ∀ x, W (A x) = A (W x)) (k : ℕ) (x : E) :
    (W : E → E)^[k] (A x) = A ((W : E → E)^[k] x) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [Function.iterate_succ_apply', ih, hcomm]

theorem operator_polynomial_commutes (A W : E →L[ℝ] E)
    (hcomm : ∀ x, W (A x) = A (W x)) (p : ℝ[X]) (x : E) :
    (Polynomial.aeval W p) (A x) = A ((Polynomial.aeval W p) x) := by
  induction p using Polynomial.induction_on' with
  | h_add p q hp hq => simp only [map_add, ContinuousLinearMap.add_apply, hp, hq]
  | h_monomial k c =>
    simp only [Polynomial.aeval_monomial, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.algebraMap_apply, ContinuousLinearMap.coe_pow, map_smul,
      operator_iterate_commutes A W hcomm]

theorem operator_polynomial_limit_commutes (A W : E →L[ℝ] E)
    (hcomm : ∀ x, W (A x) = A (W x)) (p : ℕ → ℝ[X]) (S : E →L[ℝ] E)
    (hS : Tendsto (fun n => Polynomial.aeval W (p n)) atTop (𝓝 S)) (x : E) :
    S (A x) = A (S x) := by
  have hl := operator_limit_apply hS (A x)
  have hr := (A.continuous.tendsto (S x)).comp (operator_limit_apply hS x)
  have he : (fun n => (Polynomial.aeval W (p n)) (A x)) =
      (fun n => A ((Polynomial.aeval W (p n)) x)) :=
    funext (fun n => operator_polynomial_commutes A W hcomm (p n) x)
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

set_option maxHeartbeats 1200000 in
/-- A bounded positive symmetric operator has an actual bounded symmetric
square root, with the exact norm-comparison constants. The construction
commutes with every bounded operator commuting with the original operator. -/
theorem positive_operator_square_root_exists [CompleteSpace E]
    (W : E →L[ℝ] E) (hW : W.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,W x⟫ ∧ ⟪x,W x⟫ ≤ b*‖x‖^2) :
    ∃ S : E →L[ℝ] E,
      S.toLinearMap.IsSymmetric ∧ W = S.comp S ∧
      (∀ x, Real.sqrt a * ‖x‖^2 ≤ ⟪x,S x⟫ ∧ ⟪x,S x⟫ ≤ Real.sqrt b * ‖x‖^2) ∧
      (∀ x, Real.sqrt a * ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ Real.sqrt b * ‖x‖) ∧
      IsUnit S ∧
      (∀ A : E →L[ℝ] E, (∀ x, W (A x) = A (W x)) → ∀ x, S (A x) = A (S x)) := by
  let f : C(Icc a b, ℝ) := ⟨fun t => Real.sqrt (t : ℝ),
    Real.continuous_sqrt.comp continuous_subtype_val⟩
  have hf2 : f * f = intervalCoordinate a b := by
    ext t
    exact Real.mul_self_sqrt (ha.le.trans t.2.1)
  obtain ⟨p,S,hp,hS⟩ := operator_polynomial_limit_exists W hW a b hbounds f
  have hsym := operator_polynomial_limit_symmetric W hW p S hS
  have hdiff : Tendsto (fun n => (p n * p n - Polynomial.X).toContinuousMapOn (Icc a b))
      atTop (𝓝 (0 : C(Icc a b, ℝ))) := by
    have he (n : ℕ) : (p n * p n - Polynomial.X).toContinuousMapOn (Icc a b) =
        (p n).toContinuousMapOn (Icc a b) * (p n).toContinuousMapOn (Icc a b) -
          intervalCoordinate a b := by ext t; simp [intervalCoordinate]
    simpa only [he, hf2, sub_self] using (hp.mul hp).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => intervalCoordinate a b) atTop (𝓝 (intervalCoordinate a b)))
  have hsq : Tendsto (fun n => Polynomial.aeval W (p n) * Polynomial.aeval W (p n))
      atTop (𝓝 W) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_)
      (by simpa only [norm_zero] using hdiff.norm)
    exact polynomial_square_operator_error W hW a b hbounds (p n)
  have hsquare : W = S.comp S := (tendsto_nhds_unique (hS.mul hS) hsq).symm
  have hform : ∀ x, Real.sqrt a * ‖x‖^2 ≤ ⟪x,S x⟫ ∧ ⟪x,S x⟫ ≤ Real.sqrt b * ‖x‖^2 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    let L := operatorMomentState W hW a b hbounds x hx
    have hl : Real.sqrt a ≤ L.1 f := by
      have h := positive_unit_mono L.2 (f := ContinuousMap.const (Icc a b) (Real.sqrt a))
        (g := f) (fun t => Real.sqrt_le_sqrt t.2.1)
      simpa only [positive_unit_const L.2] using h
    have hu : L.1 f ≤ Real.sqrt b := by
      have h := positive_unit_mono L.2 (f := f)
        (g := ContinuousMap.const (Icc a b) (Real.sqrt b)) (fun t => Real.sqrt_le_sqrt t.2.2)
      simpa only [positive_unit_const L.2] using h
    rw [operator_polynomial_limit_form W hW a b hbounds f p S hp hS x hx]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hl (sq_nonneg ‖x‖)]
    · nlinarith [mul_le_mul_of_nonneg_left hu (sq_nonneg ‖x‖)]
  have hnorm : ∀ x, Real.sqrt a * ‖x‖ ≤ ‖S x‖ ∧ ‖S x‖ ≤ Real.sqrt b * ‖x‖ := by
    intro x
    have he : ‖S x‖^2 = ⟪x,W x⟫ := by
      rw [hsquare]
      change ‖S x‖^2 = ⟪x,S (S x)⟫
      calc
        ‖S x‖^2 = ⟪S x,S x⟫ := (real_inner_self_eq_norm_sq _).symm
        _ = ⟪x,S (S x)⟫ := hsym x (S x)
    constructor
    · have hsq' : (Real.sqrt a * ‖x‖)^2 ≤ ‖S x‖^2 := by
        rw [mul_pow, Real.sq_sqrt ha.le, he]
        exact (hbounds x).1
      have h := sq_le_sq.mp hsq'
      simpa only [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg a) (norm_nonneg x)),
        abs_of_nonneg (norm_nonneg (S x))] using h
    · have hsq' : ‖S x‖^2 ≤ (Real.sqrt b * ‖x‖)^2 := by
        rw [mul_pow, Real.sq_sqrt (ha.le.trans hab), he]
        exact (hbounds x).2
      have h := sq_le_sq.mp hsq'
      simpa only [abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg b) (norm_nonneg x)),
        abs_of_nonneg (norm_nonneg (S x))] using h
  refine ⟨S,hsym,hsquare,hform,hnorm,?_,?_⟩
  · exact coercive_operator_isUnit S (Real.sqrt a) (Real.sqrt_pos.2 ha) (fun x => (hform x).1)
  · intro A hcomm x
    exact operator_polynomial_limit_commutes A W hcomm p S hS x

end BB
