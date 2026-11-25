import BB.MidpointCriterion
import BB.NonlinearStep
import BB.QuadraticObjective

set_option autoImplicit false

noncomputable section
namespace BB.LocalSharpness
open BB.Operator BB.Secant Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem eigen_smul {H : E →ₗ[ℝ] E} {a : ℝ} {u : E}
    (hu : H u = a • u) (s : ℝ) : H (s • u) = a • (s • u) := by
  rw [H.map_smul,hu,smul_smul,smul_smul,mul_comm]

theorem eigenvector_sum_ne_zero {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≠ b) {u v : E} (hu : H u = a • u) (hv : H v = b • v)
    (hu0 : u ≠ 0) : u+v ≠ 0 := by
  intro hh
  have hnorm := two_eigenvector_norm_sq hH hab hu hv
  rw [hh,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hnorm
  nlinarith only [hnorm,sq_pos_of_pos (norm_pos_iff.mpr hu0),sq_nonneg ‖v‖]

/-- A capped first step followed by the constant midpoint step. -/
def startupSteps (a b t : ℝ) : ℕ → ℝ
  | 0 => t
  | _+1 => 2/(a+b)

/-- The exact orbit after one independently prescribed first step. This formula
can represent either point or gradient eigencomponents. -/
def startupOrbit (a b t : ℝ) (u v : E) : ℕ → E
  | 0 => u+v
  | k+1 => endpointGradient a b ((1-t*a) • u) ((1-t*b) • v) k

theorem startupOrbit_step {H : E →ₗ[ℝ] E} {a b t : ℝ}
    (ha : 0 < a) (hab : a < b) {u v : E}
    (hu : H u = a • u) (hv : H v = b • v) (k : ℕ) :
    startupOrbit a b t u v (k+1) = startupOrbit a b t u v k-
      startupSteps a b t k • H (startupOrbit a b t u v k) := by
  cases k with
  | zero =>
    simp only [startupOrbit,startupSteps,endpointGradient_zero,H.map_add,hu,hv,
      smul_add,smul_smul,sub_smul,one_smul]
    abel
  | succ k =>
    exact (endpoint_gradient_step ha hab (eigen_smul hu (1-t*a)) (eigen_smul hv (1-t*b)) k).symm

theorem startupOrbit_H (H : E →ₗ[ℝ] E) (a b t : ℝ) (u v : E) (k : ℕ) :
    H (startupOrbit a b t u v k) = startupOrbit a b t (H u) (H v) k := by
  cases k <;> simp only [startupOrbit,endpointGradient,map_add,map_smul]

theorem startupOrbit_norm_tail {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) {u v : E}
    (hu : H u = a • u) (hv : H v = b • v) (k : ℕ) :
    ‖startupOrbit a b t u v (k+1)‖ =
      BB.endpointRate a b^k*‖startupOrbit a b t u v 1‖ := by
  simpa only [startupOrbit,endpointGradient_zero] using
    endpoint_norm hH ha hab (eigen_smul hu (1-t*a)) (eigen_smul hv (1-t*b)) k

theorem startupOrbit_ne_zero {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : 0 < t) (htb : t < 1/b)
    {u v : E} (hu : H u = a • u) (hv : H v = b • v) (hu0 : u ≠ 0) (k : ℕ) :
    startupOrbit a b t u v k ≠ 0 := by
  have hta : t*a < 1 := (mul_lt_mul_of_pos_left hab ht).trans ((lt_div_iff (ha.trans hab)).mp htb)
  have hU : (1-t*a) • u ≠ 0 := smul_ne_zero (ne_of_gt (sub_pos.mpr hta)) hu0
  cases k with
  | zero => exact eigenvector_sum_ne_zero hH hab.ne hu hv hu0
  | succ k =>
    apply norm_pos_iff.mp
    rw [startupOrbit_norm_tail hH ha hab hu hv]
    apply mul_pos (pow_pos (BB.endpointRate_pos ha hab) k)
    apply norm_pos_iff.mpr
    simp only [startupOrbit,endpointGradient_zero]
    exact eigenvector_sum_ne_zero hH hab.ne (eigen_smul hu (1-t*a)) (eigen_smul hv (1-t*b)) hU

theorem startupOrbit_norm_le_initial {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : 0 < t) (htb : t < 1/b)
    {u v : E} (hu : H u = a • u) (hv : H v = b • v) (k : ℕ) :
    ‖startupOrbit a b t u v k‖ ≤ ‖u+v‖ := by
  have hb := ha.trans hab
  have htb' := (lt_div_iff hb).mp htb
  have hta := (mul_lt_mul_of_pos_left hab ht).trans htb'
  have hpa : 0 ≤ 1-t*a := (sub_pos.mpr hta).le
  have hpb : 0 ≤ 1-t*b := (sub_pos.mpr htb').le
  have hpa1 : (1-t*a)^2 ≤ 1 := by nlinarith only [hpa,mul_pos ht ha]
  have hpb1 : (1-t*b)^2 ≤ 1 := by nlinarith only [hpb,mul_pos ht hb]
  have hfirst : ‖startupOrbit a b t u v 1‖ ≤ ‖u+v‖ := by
    simp only [startupOrbit,endpointGradient_zero]
    have hnorm := two_eigenvector_norm_sq hH hab.ne (eigen_smul hu (1-t*a)) (eigen_smul hv (1-t*b))
    have hnorm0 := two_eigenvector_norm_sq hH hab.ne hu hv
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hnorm
    have h1 := mul_le_mul_of_nonneg_right hpa1 (sq_nonneg ‖u‖)
    have h2 := mul_le_mul_of_nonneg_right hpb1 (sq_nonneg ‖v‖)
    nlinarith only [hnorm,hnorm0,h1,h2,norm_nonneg ((1-t*a) • u+(1-t*b) • v),norm_nonneg (u+v)]
  cases k with
  | zero => exact le_refl _
  | succ k =>
    rw [startupOrbit_norm_tail hH ha hab hu hv]
    calc
      BB.endpointRate a b^k*‖startupOrbit a b t u v 1‖ ≤ 1*‖startupOrbit a b t u v 1‖ :=
        mul_le_mul_of_nonneg_right
          (pow_le_one k (BB.endpointRate_pos ha hab).le (BB.endpointRate_lt_one ha hab).le)
          (norm_nonneg _)
      _ ≤ ‖u+v‖ := by simpa only [one_mul] using hfirst

/-- Midpoint admissibility survives every sign change and radial contraction of
the endpoint orbit. -/
theorem endpoint_midpoint_interval {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : E}
    (hu : H u = a • u) (hv : H v = b • v) (hu0 : u ≠ 0)
    (hlo : a*‖u‖^2 ≤ b*‖v‖^2) (hhi : ‖v‖^2 ≤ ‖u‖^2) (k : ℕ) :
    bb2 (endpointGradient a b u v k) (H (endpointGradient a b u v k)) ≤ 2/(a+b) ∧
      2/(a+b) ≤ bb1 (endpointGradient a b u v k) (H (endpointGradient a b u v k)) := by
  have hc := BB.endpointRate_pos ha hab
  have hneg : ((-BB.endpointRate a b)^k)^2 = (BB.endpointRate a b^k)^2 := by
    rw [← sq_abs,abs_pow,abs_neg,← abs_pow,sq_abs]
  apply (midpoint_interval_iff_energy hH ha hab
    (eigen_smul hu (BB.endpointRate a b^k)) (eigen_smul hv ((-BB.endpointRate a b)^k))
    (smul_ne_zero (pow_ne_zero k hc.ne') hu0)).mpr
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hneg]
  have h1 := mul_le_mul_of_nonneg_left hlo (sq_nonneg (BB.endpointRate a b^k))
  have h2 := mul_le_mul_of_nonneg_left hhi (sq_nonneg (BB.endpointRate a b^k))
  constructor <;> nlinarith only [h1,h2]

/-- Every preceding gradient generated by the small startup step permits the
constant midpoint choice. -/
theorem startupOrbit_midpoint_interval {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {a b t : ℝ} (ha : 0 < a) (hab : a < b) (ht : 0 < t) (htb : t < 1/b)
    (htlo : a*(1-t*a)^2 ≤ b*(1-t*b)^2) (hthi : (1-t*b)^2 ≤ (1-t*a)^2)
    {u v : E} (hu : H u = a • u) (hv : H v = b • v) (hu0 : u ≠ 0)
    (hbal : ‖u‖^2 = ‖v‖^2) (k : ℕ) :
    bb2 (startupOrbit a b t u v k) (H (startupOrbit a b t u v k)) ≤ 2/(a+b) ∧
      2/(a+b) ≤ bb1 (startupOrbit a b t u v k) (H (startupOrbit a b t u v k)) := by
  cases k with
  | zero =>
    apply (midpoint_interval_iff_energy hH ha hab hu hv hu0).mpr
    rw [hbal]
    exact ⟨mul_le_mul_of_nonneg_right hab.le (sq_nonneg _),le_refl _⟩
  | succ k =>
    have hta : t*a < 1 := (mul_lt_mul_of_pos_left hab ht).trans ((lt_div_iff (ha.trans hab)).mp htb)
    apply endpoint_midpoint_interval hH ha hab (eigen_smul hu (1-t*a)) (eigen_smul hv (1-t*b))
      (smul_ne_zero (ne_of_gt (sub_pos.mpr hta)) hu0) ?_ ?_ k
    · simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← hbal]
      have hh := mul_le_mul_of_nonneg_right htlo (sq_nonneg ‖u‖)
      nlinarith only [hh]
    · simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,← hbal]
      exact mul_le_mul_of_nonneg_right hthi (sq_nonneg ‖u‖)

/-- The interval for actual secants agrees with the interval for the preceding
gradient on a quadratic, after cancelling the nonzero step length. -/
theorem quadratic_intervalChoice (H : E →ₗ[ℝ] E) {x : ℕ → E} {alpha : ℕ → ℝ}
    (hpositive : ∀ k, 0 < alpha k)
    (hrec : ∀ k, x (k+1) = x k-alpha k • H (x k))
    (hinterval : ∀ k, bb2 (H (x k)) (H (H (x k))) ≤ alpha (k+1) ∧
      alpha (k+1) ≤ bb1 (H (x k)) (H (H (x k)))) :
    ∀ k, BB.Local.intervalChoice H (x k) (x (k+1)) (alpha (k+1)) := by
  intro k _
  have hs : x (k+1)-x k = (-alpha k) • H (x k) := by rw [hrec,neg_smul]; abel
  have hy : H (x (k+1))-H (x k) = (-alpha k) • H (H (x k)) := by
    rw [← H.map_sub,hs,H.map_smul]
  rw [hs,hy,bb1_smul _ _ (neg_ne_zero.mpr (hpositive k).ne'),
    bb2_smul _ _ (neg_ne_zero.mpr (hpositive k).ne')]
  exact hinterval k

/-- A single exact nonzero critical-rate tail rules out every smaller global
factor, independently of its first step. -/
theorem no_smaller_factor_of_exact_tail (y : ℕ → E) {c : ℝ} (hc : 0 < c)
    (hy : y 1 ≠ 0) (htail : ∀ k : ℕ, ‖y (k+1)‖ = c^k*‖y 1‖)
    {r : ℝ} (hr : 0 ≤ r) (hrc : r < c) :
    ¬ ∃ K : ℝ, ∀ k : ℕ, ‖y k‖ ≤ K*r^k*‖y 0‖ := by
  have hG := norm_pos_iff.mpr hy
  rintro ⟨K,hK⟩
  by_cases hrzero : r = 0
  · have hh := hK 1
    simp only [hrzero,zero_pow (by decide : 1 ≠ 0),mul_zero,zero_mul] at hh
    exact (not_le_of_gt hG) hh
  have hrpos := lt_of_le_of_ne hr (Ne.symm hrzero)
  let L := K*r*‖y 0‖/‖y 1‖
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt L ((one_lt_div hrpos).mpr hrc)
  have hh := hK (k+1)
  rw [htail,pow_succ] at hh
  have hpow : c^k ≤ L*r^k := by
    apply (mul_le_mul_right hG).mp
    calc
      c^k*‖y 1‖ ≤ K*(r^k*r)*‖y 0‖ := hh
      _ = (L*r^k)*‖y 1‖ := by dsimp [L]; field_simp; ring
  have hdiv : (c/r)^k ≤ L := by
    rw [div_pow]
    exact (div_le_iff (pow_pos hrpos k)).mpr hpow
  exact (not_lt_of_ge hdiv) hk

/-- Sharpness for an arbitrary first-step cap and an arbitrary neighborhood,
on the actual point iteration of any prescribed Hessian with the two specified
positive eigenvalues. The whole orbit stays inside the prescribed neighborhood. -/
theorem local_sharpness_operator (H : E →ₗ[ℝ] E) (hH : H.IsSymmetric)
    {a b A₀ delta : ℝ} (ha : 0 < a) (hab : a < b)
    (haeig : HasEigenvalue H a) (hbeig : HasEigenvalue H b)
    (hA₀ : 0 < A₀) (hdelta : 0 < delta) :
    ∃ x : ℕ → E, ∃ alpha : ℕ → ℝ,
      x 0 ≠ 0 ∧ ‖x 0‖ < delta ∧
      (∀ k, 0 < alpha k) ∧ alpha 0 ≤ A₀ ∧
      (∀ k, alpha (k+1) = 2/(a+b)) ∧
      (∀ k, x (k+1) = x k-alpha k • H (x k)) ∧
      (∀ k, BB.Local.intervalChoice H (x k) (x (k+1)) (alpha (k+1))) ∧
      (∀ k, ‖x k‖ < delta) ∧
      (∀ k, H (x k) ≠ 0) ∧
      (∀ k, ‖H (x (k+1))‖ = BB.endpointRate a b^k*‖H (x 1)‖) ∧
      (∀ k, ‖x (k+1)‖ = BB.endpointRate a b^k*‖x 1‖) ∧
      (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate a b →
        ¬ ∃ K : ℝ, ∀ k : ℕ, ‖H (x k)‖ ≤ K*r^k*‖H (x 0)‖) ∧
      (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate a b →
        ¬ ∃ K : ℝ, ∀ k : ℕ, ‖x k‖ ≤ K*r^k*‖x 0‖) := by
  have hidpd : ∀ z : E, z ≠ 0 → 0 < @inner ℝ _ _ z ((LinearMap.id : E →ₗ[ℝ] E) z) := by
    intro z hz
    simpa only [LinearMap.id_apply,real_inner_self_eq_norm_sq] using
      sq_pos_of_pos (norm_pos_iff.mpr hz)
  obtain ⟨u₀,v₀,hu₀0,hv₀0,hu₀,hv₀,hbalance⟩ :=
    exists_balanced_eigenvectors haeig hbeig hidpd
  simp only [LinearMap.id_apply,real_inner_self_eq_norm_sq] at hbalance
  obtain ⟨t,ht,htA,htb,htlo,hthi⟩ := exists_small_first_step ha hab hA₀
  have hb := ha.trans hab
  let p₀ := (1/a) • u₀+(1/b) • v₀
  let sigma := delta/(2*(‖p₀‖+1))
  have hden : 0 < 2*(‖p₀‖+1) := by positivity
  have hsigma : 0 < sigma := div_pos hdelta hden
  let u := sigma • u₀
  let v := sigma • v₀
  have hu : H u = a • u := eigen_smul hu₀ sigma
  have hv : H v = b • v := eigen_smul hv₀ sigma
  have hu0 : u ≠ 0 := smul_ne_zero hsigma.ne' hu₀0
  have hbal : ‖u‖^2 = ‖v‖^2 := by
    dsimp [u,v]
    simp only [norm_smul,mul_pow,hbalance]
  let p := (1/a) • u
  let q := (1/b) • v
  have hp : H p = a • p := eigen_smul hu (1/a)
  have hq : H q = b • q := eigen_smul hv (1/b)
  have hp0 : p ≠ 0 := smul_ne_zero (one_div_ne_zero ha.ne') hu0
  have hHp : H p = u := by
    dsimp [p]
    rw [H.map_smul,hu,smul_smul,one_div_mul_cancel ha.ne',one_smul]
  have hHq : H q = v := by
    dsimp [q]
    rw [H.map_smul,hv,smul_smul,one_div_mul_cancel hb.ne',one_smul]
  have hscale : p+q = sigma • p₀ := by
    dsimp [p,q,p₀,u,v]
    rw [smul_add]
    congr 1 <;> rw [smul_smul,smul_smul,mul_comm]
  have hsmall : ‖p+q‖ < delta := by
    rw [hscale,norm_smul,Real.norm_eq_abs,abs_of_pos hsigma]
    have heq : sigma*(2*(‖p₀‖+1)) = delta := by dsimp [sigma]; field_simp
    have hh := mul_nonneg hsigma.le (norm_nonneg p₀)
    nlinarith only [heq,hh,hsigma]
  let x := startupOrbit a b t p q
  let alpha := startupSteps a b t
  have hpositive : ∀ k, 0 < alpha k := by
    intro k
    cases k with
    | zero => exact ht
    | succ k => exact div_pos (by norm_num) (add_pos ha hb)
  have hrec : ∀ k, x (k+1) = x k-alpha k • H (x k) := startupOrbit_step ha hab hp hq
  have hgradient (k : ℕ) : H (x k) = startupOrbit a b t u v k := by
    dsimp [x]
    rw [startupOrbit_H,hHp,hHq]
  have hnonzero : ∀ k, H (x k) ≠ 0 := by
    intro k
    rw [hgradient]
    exact startupOrbit_ne_zero hH ha hab ht htb hu hv hu0 k
  have hxtail : ∀ k, ‖x (k+1)‖ = BB.endpointRate a b^k*‖x 1‖ :=
    startupOrbit_norm_tail hH ha hab hp hq
  have hgtail : ∀ k, ‖H (x (k+1))‖ = BB.endpointRate a b^k*‖H (x 1)‖ := by
    intro k
    rw [hgradient,hgradient]
    exact startupOrbit_norm_tail hH ha hab hu hv k
  have hxone : x 1 ≠ 0 := startupOrbit_ne_zero hH ha hab ht htb hp hq hp0 1
  refine ⟨x,alpha,startupOrbit_ne_zero hH ha hab ht htb hp hq hp0 0,hsmall,hpositive,htA,
    (fun _ => rfl),hrec,?_,?_,hnonzero,hgtail,hxtail,?_,?_⟩
  · apply quadratic_intervalChoice H hpositive hrec
    intro k
    rw [hgradient]
    exact startupOrbit_midpoint_interval hH ha hab ht htb htlo hthi hu hv hu0 hbal k
  · intro k
    exact (startupOrbit_norm_le_initial hH ha hab ht htb hp hq k).trans_lt hsmall
  · intro r hr hrc
    exact no_smaller_factor_of_exact_tail (fun k => H (x k)) (BB.endpointRate_pos ha hab)
      (hnonzero 1) hgtail hr hrc
  · intro r hr hrc
    exact no_smaller_factor_of_exact_tail x (BB.endpointRate_pos ha hab) hxone hxtail hr hrc

/-- Fully instantiated local sharpness for the smooth strictly convex quadratic
with the prescribed positive definite Hessian, and every positive startup cap. -/
theorem local_sharpness_quadratic [CompleteSpace E]
    (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    (hpd : ∀ z : E, z ≠ 0 → 0 < @inner ℝ _ _ z (H z))
    {a b A₀ : ℝ} (ha : 0 < a) (hab : a < b)
    (haeig : HasEigenvalue H.toLinearMap a) (hbeig : HasEigenvalue H.toLinearMap b)
    (hA₀ : 0 < A₀) :
    ContDiff ℝ ⊤ (BB.Quadratic.objective H) ∧
      gradient (BB.Quadratic.objective H) = H ∧
      (∀ z : E, fderiv ℝ (gradient (BB.Quadratic.objective H)) z = H) ∧
      (∀ z : E, z ≠ 0 → 0 < BB.Quadratic.objective H z) ∧
      ∀ delta : ℝ, 0 < delta → ∃ x : ℕ → E, ∃ alpha : ℕ → ℝ,
        x 0 ≠ 0 ∧ ‖x 0‖ < delta ∧
        (∀ k, 0 < alpha k) ∧ alpha 0 ≤ A₀ ∧
        (∀ k, alpha (k+1) = 2/(a+b)) ∧
        (∀ k, x (k+1) = x k-alpha k • gradient (BB.Quadratic.objective H) (x k)) ∧
        (∀ k, BB.Local.intervalChoice (gradient (BB.Quadratic.objective H))
          (x k) (x (k+1)) (alpha (k+1))) ∧
        (∀ k, ‖x k‖ < delta) ∧
        (∀ k, gradient (BB.Quadratic.objective H) (x k) ≠ 0) ∧
        (∀ k, ‖gradient (BB.Quadratic.objective H) (x (k+1))‖ =
          BB.endpointRate a b^k*‖gradient (BB.Quadratic.objective H) (x 1)‖) ∧
        (∀ k, ‖x (k+1)‖ = BB.endpointRate a b^k*‖x 1‖) ∧
        (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate a b →
          ¬ ∃ K : ℝ, ∀ k : ℕ, ‖gradient (BB.Quadratic.objective H) (x k)‖ ≤
            K*r^k*‖gradient (BB.Quadratic.objective H) (x 0)‖) ∧
        (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate a b →
          ¬ ∃ K : ℝ, ∀ k : ℕ, ‖x k‖ ≤ K*r^k*‖x 0‖) := by
  refine ⟨BB.Quadratic.objective_contDiff H ⊤,BB.Quadratic.objective_gradient H hH,
    BB.Quadratic.objective_hessian H hH,fun z hz => BB.Quadratic.objective_pos H hpd hz,?_⟩
  intro delta hdelta
  simpa only [BB.Quadratic.objective_gradient H hH] using
    local_sharpness_operator H.toLinearMap hH ha hab haeig hbeig hA₀ hdelta

end BB.LocalSharpness
