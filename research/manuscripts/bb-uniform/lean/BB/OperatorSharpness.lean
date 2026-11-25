import BB.OperatorCondition
import BB.Sharpness

set_option autoImplicit false

noncomputable section
namespace BB.Operator
open Module.End

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Eigenvectors belonging to distinct eigenvalues of a symmetric operator are orthogonal. -/
theorem eigenvectors_inner_eq_zero {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {a b : ℝ} (hab : a ≠ b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) : @inner ℝ _ _ u v = 0 := by
  have hh := hH u v
  rw [hu,hv,real_inner_smul_left,inner_smul_right] at hh
  have hmul : (a-b)*@inner ℝ _ _ u v = 0 := by linarith only [hh]
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hab)

/-- Commutation makes the weighted cross term between distinct eigenspaces vanish. -/
theorem weighted_eigenvectors_inner_eq_zero {H W : V →ₗ[ℝ] V}
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    {a b : ℝ} (hab : a ≠ b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) : @inner ℝ _ _ u (W v) = 0 := by
  apply eigenvectors_inner_eq_zero hH hab hu
  rw [hcomm v,hv,W.map_smul]

theorem energy_smul (W : V →ₗ[ℝ] V) (r : ℝ) (u : V) :
    @inner ℝ _ _ (r • u) (W (r • u)) = r^2 * @inner ℝ _ _ u (W u) := by
  rw [W.map_smul,real_inner_smul_left,inner_smul_right]
  ring

/-- The weighted quadratic form has no mixed term on two distinct eigenspaces. -/
theorem two_eigenvector_energy {H W : V →ₗ[ℝ] V}
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    {a b : ℝ} (hab : a ≠ b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) (x y : ℝ) :
    @inner ℝ _ _ (x • u+y • v) (W (x • u+y • v)) =
      x^2*@inner ℝ _ _ u (W u)+y^2*@inner ℝ _ _ v (W v) := by
  have huv := weighted_eigenvectors_inner_eq_zero hH hcomm hab hu hv
  have hvu := weighted_eigenvectors_inner_eq_zero hH hcomm hab.symm hv hu
  simp only [map_add,map_smul,inner_add_left,inner_add_right,
    real_inner_smul_left,inner_smul_right,huv,hvu,mul_zero,zero_mul,add_zero,zero_add]
  ring

/-- The actual operator quotient on an endpoint plane is the weighted two-dimensional quotient. -/
theorem weightedAlpha_two_eigenvectors {H W : V →ₗ[ℝ] V}
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    {a b : ℝ} (hab : a ≠ b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) (x y : ℝ) :
    weightedAlpha H W (x • u+y • v) =
      BB.Spectral.vectorAlpha (BB.Sharpness.twoSpectrum a b)
        (BB.Sharpness.twoWeights (@inner ℝ _ _ u (W u)) (@inner ℝ _ _ v (W v))) ![x,y] := by
  have huv := weighted_eigenvectors_inner_eq_zero hH hcomm hab hu hv
  have hvu := weighted_eigenvectors_inner_eq_zero hH hcomm hab.symm hv hu
  unfold weightedAlpha BB.Spectral.vectorAlpha BB.Spectral.quadraticForm
  simp only [Fin.sum_univ_two,BB.Sharpness.twoSpectrum,BB.Sharpness.twoWeights,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  rw [two_eigenvector_energy hH hcomm hab hu hv]
  simp only [map_add,map_smul,hu,hv,smul_smul,inner_add_left,inner_add_right,
    real_inner_smul_left,inner_smul_right,huv,hvu,mul_zero,zero_mul,add_zero,zero_add]
  congr 1 <;> ring

/-- Explicit endpoint orbit in the original Hilbert space. -/
def endpointGradient (a b : ℝ) (u v : V) (k : ℕ) : V :=
  BB.endpointRate a b^k • u+(-BB.endpointRate a b)^k • v

/-- The preceding gradient is repeated at time zero, as required by matched initialization. -/
def endpointState (a b : ℝ) (u v : V) (k : ℕ) : V × V :=
  (endpointGradient a b u v (k-1),endpointGradient a b u v k)

@[simp] theorem endpointGradient_zero (a b : ℝ) (u v : V) :
    endpointGradient a b u v 0 = u+v := by simp [endpointGradient]

@[simp] theorem endpointState_zero (a b : ℝ) (u v : V) :
    endpointState a b u v 0 = (u+v,u+v) := by simp [endpointState]

/-- Equal endpoint energies force the midpoint reciprocal stepsize at every time. -/
theorem endpoint_quotient {H W : V →ₗ[ℝ] V}
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v)
    (hEu : 0 < @inner ℝ _ _ u (W u))
    (hbal : @inner ℝ _ _ u (W u) = @inner ℝ _ _ v (W v)) (k : ℕ) :
    weightedAlpha H W (endpointGradient a b u v k) = 2/(a+b) := by
  rw [endpointGradient,weightedAlpha_two_eigenvectors hH hcomm hab.ne hu hv]
  have hh := BB.Sharpness.balanced_quotient (a := a) (b := b)
    (wa := @inner ℝ _ _ u (W u)) (wb := @inner ℝ _ _ v (W v))
    (x := 1) (y := 1) ha hab hEu (by norm_num) (by simpa using hbal) k
  simpa only [BB.Sharpness.balancedGradient,mul_one] using hh

/-- The endpoint orbit obeys the actual original-space gradient update. -/
theorem endpoint_gradient_step {H : V →ₗ[ℝ] V}
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) (k : ℕ) :
    endpointGradient a b u v k-(2/(a+b)) • H (endpointGradient a b u v k) =
      endpointGradient a b u v (k+1) := by
  obtain ⟨hlo,hhi⟩ := BB.Sharpness.midpoint_multipliers ha hab
  simp only [endpointGradient,map_add,map_smul,hu,hv,smul_add,smul_smul,pow_succ]
  have hlo' : BB.endpointRate a b^k-(2/(a+b))*(BB.endpointRate a b^k*a) =
      BB.endpointRate a b^k*BB.endpointRate a b := by
    calc
      _ = BB.endpointRate a b^k*(1-(2/(a+b))*a) := by ring
      _ = _ := by rw [hlo]
  have hhi' : (-BB.endpointRate a b)^k-(2/(a+b))*((-BB.endpointRate a b)^k*b) =
      (-BB.endpointRate a b)^k*(-BB.endpointRate a b) := by
    calc
      _ = (-BB.endpointRate a b)^k*(1-(2/(a+b))*b) := by ring
      _ = _ := by rw [hhi]
  rw [add_sub_add_comm,← sub_smul,← sub_smul,hlo',hhi']

/-- Exact delayed weighted BB recurrence, including matched initialization. -/
theorem endpoint_state_recurrence {H W : V →ₗ[ℝ] V}
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v)
    (hEu : 0 < @inner ℝ _ _ u (W u))
    (hbal : @inner ℝ _ _ u (W u) = @inner ℝ _ _ v (W v)) (k : ℕ) :
    stateMap H W (endpointState a b u v k) = endpointState a b u v (k+1) := by
  unfold endpointState stateMap
  rw [endpoint_quotient hH hcomm ha hab hu hv hEu hbal,endpoint_gradient_step ha hab hu hv]
  simp

/-- Orthogonality gives the exact norm formula in the original Euclidean space. -/
theorem endpoint_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) (k : ℕ) :
    ‖endpointGradient a b u v k‖ = BB.endpointRate a b^k*‖u+v‖ := by
  have huv := eigenvectors_inner_eq_zero hH hab.ne hu hv
  have hnorm0 : ‖u+v‖^2 = ‖u‖^2+‖v‖^2 := by
    simpa only [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_real huv
  have hneg : |(-BB.endpointRate a b)^k| = BB.endpointRate a b^k := by
    rw [abs_pow,abs_neg,abs_of_nonneg (BB.endpointRate_pos ha hab).le]
  have hpos : |BB.endpointRate a b^k| = BB.endpointRate a b^k :=
    abs_of_nonneg (pow_nonneg (BB.endpointRate_pos ha hab).le k)
  have hnorm : ‖endpointGradient a b u v k‖^2 = (BB.endpointRate a b^k)^2*‖u+v‖^2 := by
    unfold endpointGradient
    rw [norm_add_sq_real,real_inner_smul_left,inner_smul_right,huv,
      mul_zero,mul_zero,mul_zero,add_zero,norm_smul,norm_smul,
      Real.norm_eq_abs,Real.norm_eq_abs,hneg,hpos,hnorm0]
    ring
  have hnonneg := mul_nonneg (pow_nonneg (BB.endpointRate_pos ha hab).le k) (norm_nonneg (u+v))
  nlinarith only [hnorm,hnonneg,norm_nonneg (endpointGradient a b u v k)]

/-- Every positive weight can be balanced on any two nonzero eigenspaces. -/
theorem exists_balanced_eigenvectors {H W : V →ₗ[ℝ] V}
    {a b : ℝ} (haeig : HasEigenvalue H a) (hbeig : HasEigenvalue H b)
    (hWpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (W x)) :
    ∃ u v : V, u ≠ 0 ∧ v ≠ 0 ∧ H u = a • u ∧ H v = b • v ∧
      @inner ℝ _ _ u (W u) = @inner ℝ _ _ v (W v) := by
  obtain ⟨u,hu⟩ := haeig.exists_hasEigenvector
  obtain ⟨v,hv⟩ := hbeig.exists_hasEigenvector
  have hEu := hWpd u hu.2
  have hEv := hWpd v hv.2
  refine ⟨Real.sqrt (@inner ℝ _ _ v (W v)) • u,
    Real.sqrt (@inner ℝ _ _ u (W u)) • v,?_,?_,?_,?_,?_⟩
  · exact smul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hEv)) hu.2
  · exact smul_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hEu)) hv.2
  · rw [H.map_smul,hu.apply_eq_smul,smul_smul,smul_smul,mul_comm]
  · rw [H.map_smul,hv.apply_eq_smul,smul_smul,smul_smul,mul_comm]
  · rw [energy_smul,energy_smul,Real.sq_sqrt hEv.le,Real.sq_sqrt hEu.le,mul_comm]

/-- No finite prefactor can compensate for a strictly smaller exponential factor. -/
theorem endpoint_no_smaller_factor {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) {u v : V}
    (hu : H u = a • u) (hv : H v = b • v) (huv : u+v ≠ 0)
    {r : ℝ} (hr : 0 ≤ r) (hrc : r < BB.endpointRate a b) :
    ¬ ∃ K : ℝ, ∀ k : ℕ, ‖endpointGradient a b u v k‖ ≤ K*r^k*‖u+v‖ := by
  have hG : 0 < ‖u+v‖ := norm_pos_iff.mpr huv
  rintro ⟨K,hK⟩
  by_cases hr0 : r = 0
  · have hh := hK 1
    rw [endpoint_norm hH ha hab hu hv,hr0] at hh
    norm_num at hh
    exact (not_le_of_gt (mul_pos (BB.endpointRate_pos ha hab) hG)) hh
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt K ((one_lt_div hrp).mpr hrc)
  have hh := hK k
  rw [endpoint_norm hH ha hab hu hv] at hh
  have hpow := (mul_le_mul_right hG).mp hh
  have hdiv : (BB.endpointRate a b/r)^k ≤ K := by
    rw [div_pow]
    exact (div_le_iff (pow_pos hrp k)).mpr hpow
  exact (not_lt_of_ge hdiv) hk

/-- Sharpness for every fixed positive commuting weight and every symmetric Hessian
having the two prescribed positive endpoint eigenvalues. -/
theorem sharp_fixed_weight {H W : V →ₗ[ℝ] V}
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    (hWpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (haeig : HasEigenvalue H a) (hbeig : HasEigenvalue H b) :
    ∃ g : ℕ → V, g 0 ≠ 0 ∧
      (∀ k, weightedAlpha H W (g k) = 2/(a+b)) ∧
      (∀ k, stateMap H W (g (k-1),g k) = (g k,g (k+1))) ∧
      (∀ k, ‖g k‖ = BB.endpointRate a b^k*‖g 0‖) ∧
      (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate a b →
        ¬ ∃ K : ℝ, ∀ k : ℕ, ‖g k‖ ≤ K*r^k*‖g 0‖) := by
  obtain ⟨u,v,hu0,hv0,hu,hv,hbal⟩ := exists_balanced_eigenvectors haeig hbeig hWpd
  have huv : u+v ≠ 0 := by
    intro hh
    have hs := norm_add_sq_eq_norm_sq_add_norm_sq_real (eigenvectors_inner_eq_zero hH hab.ne hu hv)
    rw [hh,norm_zero,zero_mul] at hs
    have hupos := sq_pos_of_pos (norm_pos_iff.mpr hu0)
    nlinarith only [hs,hupos,sq_nonneg ‖v‖]
  refine ⟨endpointGradient a b u v,by simpa using huv,
    endpoint_quotient hH hcomm ha hab hu hv (hWpd u hu0) hbal,?_,?_,?_⟩
  · intro k
    simpa only [endpointState,Nat.add_sub_cancel] using
      endpoint_state_recurrence hH hcomm ha hab hu hv (hWpd u hu0) hbal k
  · intro k
    simpa only [endpointGradient_zero] using endpoint_norm hH ha hab hu hv k
  · intro r hr hrc
    simpa only [endpointGradient_zero] using endpoint_no_smaller_factor hH ha hab hu hv huv hr hrc

/-- The sharp orbit uses the actual smallest and largest eigenvalues of any fixed
finite-dimensional positive definite Hessian. -/
theorem sharp_fixed_weight_extremes [FiniteDimensional ℝ V]
    {H W : V →ₗ[ℝ] V} [Nonempty (Eigenvalues H)]
    (hH : H.IsSymmetric) (hcomm : Function.Commute H W)
    (hHpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    (hWpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    (hsep : spectralMin H < spectralMax H) :
    ∃ g : ℕ → V, g 0 ≠ 0 ∧
      (∀ k, weightedAlpha H W (g k) = 2/(spectralMin H+spectralMax H)) ∧
      (∀ k, stateMap H W (g (k-1),g k) = (g k,g (k+1))) ∧
      (∀ k, ‖g k‖ = BB.endpointRate (spectralMin H) (spectralMax H)^k*‖g 0‖) ∧
      (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate (spectralMin H) (spectralMax H) →
        ¬ ∃ K : ℝ, ∀ k : ℕ, ‖g k‖ ≤ K*r^k*‖g 0‖) :=
  sharp_fixed_weight hH hcomm hWpd (spectralMin_pos hHpd) hsep
    (Finset.univ.min' Finset.univ_nonempty : Eigenvalues H).property
    (Finset.univ.max' Finset.univ_nonempty : Eigenvalues H).property

end BB.Operator
