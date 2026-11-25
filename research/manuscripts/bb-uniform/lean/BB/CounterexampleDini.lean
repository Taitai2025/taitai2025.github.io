import BB.CounterexampleTheorem

/-! # The counterexample has no Dini Hessian modulus

Every nonnegative monotone majorant of the logarithmic modulus has a divergent
Dini integral.  This is an analytic theorem, not a declared hypothesis.
-/

noncomputable section
namespace BB.Counterexample
open Set Filter MeasureTheory
open scoped BigOperators Topology

theorem radius_zero_alpha (c r : ℝ) (n : ℕ) : radius c 0 r n = r*c^n := by
  induction n with
  | zero => simp [radius]
  | succ n ih => rw [radius_succ,ih,pow_succ]; ring

/-- No nonnegative monotone majorant of the logarithmic modulus on a neighborhood
of zero has a finite Dini integral. -/
theorem no_dini_majorant {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hmajor : ∀ t, 0 < t → t ≤ R → logModulus t ≤ omega t) :
    ¬ IntervalIntegrable (fun t => omega t/t) volume 0 R := by
  intro hDini
  let gamma : ℝ := 1/2
  have hgamma : 0 < gamma := by norm_num [gamma]
  have hgamma1 : gamma < 1 := by norm_num [gamma]
  let C := (-Real.log R-Real.log gamma)⁻¹
  have hC : 0 < C := by
    apply inv_pos.mpr
    nlinarith only [Real.log_neg hR hR1,Real.log_neg hgamma hgamma1]
  have hsample (n : ℕ) : C*(1/((n : ℝ)+1)) ≤ omega (R*gamma^n) := by
    have hl := logModulus_radius_ge_harmonic (alpha := 0) (gamma := gamma)
      hgamma hgamma1 (le_refl 0) hR hR1 hgamma1 (by simp) n
    rw [radius_zero_alpha] at hl
    have hpos : 0 < R*gamma^n := mul_pos hR (pow_pos hgamma n)
    have hle : R*gamma^n ≤ R := by
      simpa using mul_le_mul_of_nonneg_left (pow_le_one n hgamma.le hgamma1.le) hR.le
    exact hl.trans (hmajor _ hpos hle)
  let B := omega R+(∫ t in (0 : ℝ)..R,omega t/t)/(-Real.log gamma)
  have hup (n : ℕ) : C*(∑ j in Finset.range n,1/((j : ℝ)+1)) ≤ B := by
    calc
      C*(∑ j in Finset.range n,1/((j : ℝ)+1)) =
          ∑ j in Finset.range n,C*(1/((j : ℝ)+1)) := Finset.mul_sum _ _ _
      _ ≤ ∑ j in Finset.range n,omega (R*gamma^j) := Finset.sum_le_sum (fun j _ => hsample j)
      _ ≤ B := BB.Dini.geometric_sum_bound omega R gamma hR hgamma hgamma1 hmono hnonneg hDini n
  have hlim := Filter.Tendsto.const_mul_atTop hC Real.tendsto_sum_range_one_div_nat_succ_atTop
  obtain ⟨n,hn⟩ := (hlim.eventually (eventually_gt_atTop B)).exists
  exact (hup n).not_lt hn

/-- The Hessian perturbation already dominates the divergent modulus. -/
theorem no_dini_modulusDerivative_majorant {R : ℝ} (hR : 0 < R) (hR1 : R < 1)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hmajor : ∀ t, 0 < t → t ≤ R → modulusDerivative t ≤ omega t) :
    ¬ IntervalIntegrable (fun t => omega t/t) volume 0 R := by
  apply no_dini_majorant hR hR1 omega hmono hnonneg
  intro t ht htR
  have hd : logModulus t ≤ modulusDerivative t := by
    unfold modulusDerivative
    nlinarith only [sq_nonneg (logModulus t)]
  exact hd.trans (hmajor t ht htR)

/-- Testing the genuine gradient derivative on the first coordinate bounds its
operator norm below by the logarithmic Hessian perturbation. -/
theorem modulusDerivative_le_hessian_difference (a b : ℝ) {sigma t : ℝ}
    (hsigma : sigma ≠ 0) (ht : |t| < 1) :
    modulusDerivative t ≤
      ‖fderiv ℝ (coordinateGradient a b sigma) (t,0)-diagonalMap a b‖ := by
  have hz : (t,0) ∈ constructionDomain sigma := by
    exact ⟨abs_lt.mp ht,by norm_num⟩
  rw [(coordinateGradient_hasFDerivAt a b hsigma hz).fderiv]
  have hd := modulusDerivative_nonneg ht
  have hop := (diagonalMap (a-modulusDerivative t) (b+modulusDerivative (0/sigma))-
    diagonalMap a b).le_opNorm (1,0)
  simpa [diagonalMap,Prod.norm_def,Real.norm_eq_abs,abs_of_nonneg hd] using hop

/-- The actual counterexample Hessian has no Dini modulus, on any sufficiently
small ball. This concerns its genuine Fréchet derivative, not just a scalar model. -/
theorem no_dini_hessian_modulus (a b : ℝ) {sigma R : ℝ}
    (hsigma : sigma ≠ 0) (hR : 0 < R) (hR1 : R < 1)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hmajor : ∀ z : ℝ × ℝ, ‖z‖ ≤ R →
      ‖fderiv ℝ (coordinateGradient a b sigma) z-diagonalMap a b‖ ≤ omega ‖z‖) :
    ¬ IntervalIntegrable (fun t => omega t/t) volume 0 R := by
  apply no_dini_modulusDerivative_majorant hR hR1 omega hmono hnonneg
  intro t ht htR
  have htn : ‖(t,(0 : ℝ))‖=t := by simp [Prod.norm_def,Real.norm_eq_abs,abs_of_pos ht,ht.le]
  have hlo := modulusDerivative_le_hessian_difference a b hsigma
    (show |t|<1 by simpa [abs_of_pos ht] using htR.trans_lt hR1)
  have hup := hmajor (t,0) (by simpa only [htn] using htR)
  rw [htn] at hup
  exact hlo.trans hup

/-- Euclidean norm on the first coordinate axis. -/
theorem norm2_first_axis (t : ℝ) : norm2 (t,0)=|t| := by
  unfold norm2 normSq2 dot2
  simp only [mul_zero,add_zero]
  rw [← pow_two,Real.sqrt_sq_eq_abs]

/-- The genuine Hessian perturbation evaluated on a Euclidean unit vector has
size exactly d(t), independently of the ambient product norm convention. -/
theorem euclidean_hessian_axis (a b : ℝ) {sigma t : ℝ}
    (hsigma : sigma ≠ 0) (ht : |t| < 1) :
    norm2 ((fderiv ℝ (coordinateGradient a b sigma) (t,0)-diagonalMap a b) (1,0))=
      modulusDerivative t := by
  have hz : (t,0) ∈ constructionDomain sigma := ⟨abs_lt.mp ht,by norm_num⟩
  rw [(coordinateGradient_hasFDerivAt a b hsigma hz).fderiv]
  have heq : (diagonalMap (a-modulusDerivative t) (b+modulusDerivative (0/sigma))-
      diagonalMap a b) (1,0)=(-modulusDerivative t,0) := by
    ext <;> simp [diagonalMap]
  rw [heq,norm2_first_axis,abs_neg,abs_of_nonneg (modulusDerivative_nonneg ht)]

/-- No Dini modulus controls the actual Hessian in Euclidean operator norm.
The norm bound is written by its defining action on every vector. -/
theorem no_dini_euclidean_hessian_modulus (a b : ℝ) {sigma R : ℝ}
    (hsigma : sigma ≠ 0) (hR : 0 < R) (hR1 : R < 1)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (hnonneg : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (hmajor : ∀ z : ℝ × ℝ, norm2 z ≤ R → ∀ w : ℝ × ℝ,
      norm2 ((fderiv ℝ (coordinateGradient a b sigma) z-diagonalMap a b) w) ≤
        omega (norm2 z)*norm2 w) :
    ¬ IntervalIntegrable (fun t => omega t/t) volume 0 R := by
  apply no_dini_modulusDerivative_majorant hR hR1 omega hmono hnonneg
  intro t ht htR
  have htn : norm2 (t,0)=t := by rw [norm2_first_axis,abs_of_pos ht]
  have hup := hmajor (t,0) (by simpa only [htn] using htR) (1,0)
  rw [euclidean_hessian_axis a b hsigma
    (show |t|<1 by simpa [abs_of_pos ht] using htR.trans_lt hR1),htn,
    norm2_first_axis,abs_one,mul_one] at hup
  exact hup

end BB.Counterexample
