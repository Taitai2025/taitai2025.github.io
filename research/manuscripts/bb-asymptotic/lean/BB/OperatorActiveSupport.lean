import BB.OperatorSpectralMeasure
import BB.OperatorPolynomial
import BB.HilbertActive
import BB.HilbertPersistentSupport

/-!
# Intrinsic active spectral support of an actual operator trajectory

The support is that of the constructed scalar spectral probability of the
initial vector. Polynomial moment identities transfer its bounds to the actual
algebraic cyclic subspace. Consequently the active rate is proved without a
projection-valued measure or an assumed cyclic spectral representation.
-/

namespace BB
noncomputable section
open MeasureTheory Set
open scoped Polynomial
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def operatorActiveSupport (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) : Set ℝ :=
  Subtype.val '' measureSupport
    (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))

lemma operator_active_support_nonempty (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) : (operatorActiveSupport A hA a b hbounds x hx).Nonempty :=
  (probability_measureSupport_nonempty _).image _

lemma operator_active_support_subset (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) : operatorActiveSupport A hA a b hbounds x hx ⊆ Icc a b := by
  rintro _ ⟨t,_,rfl⟩
  exact t.2

lemma operator_active_support_isCompact (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) : IsCompact (operatorActiveSupport A hA a b hbounds x hx) :=
  (measureSupport_isClosed _).isCompact.image continuous_subtype_val

lemma operator_cyclic_form_bounds_of_support (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) (c d : ℝ)
    (hsupport : operatorActiveSupport A hA a b hbounds x hx ⊆ Icc c d) :
    ∀ y ∈ polynomialCyclicSpace A x, c*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ d*‖y‖^2 := by
  rintro y ⟨p,rfl⟩
  let L := operatorMomentState A hA a b hbounds x hx
  let ν := operatorSpectralProbability A hA a b hbounds x hx
  let q : C(Icc a b,ℝ) := (p.toContinuousMapOn (Icc a b))^2
  have hq : ∀ t, 0 ≤ q t := fun t => sq_nonneg _
  have hae : ∀ᵐ (t : Icc a b) ∂(ν : Measure (Icc a b)), c ≤ (t:ℝ) ∧ (t:ℝ) ≤ d :=
    (ae_mem_measureSupport (ν : Measure (Icc a b))).mono (fun t ht => hsupport ⟨t,ht,rfl⟩)
  have hlo : L.1 (c • q) ≤ L.1 (intervalCoordinate a b*q) := by
    rw [← operator_spectral_integral A hA a b hbounds x hx,
      ← operator_spectral_integral A hA a b hbounds x hx]
    apply integral_mono_ae (continuous_integrable_probability ν (c • q))
      (continuous_integrable_probability ν (intervalCoordinate a b*q))
    filter_upwards [hae] with t ht
    exact mul_le_mul_of_nonneg_right ht.1 (hq t)
  have hhi : L.1 (intervalCoordinate a b*q) ≤ L.1 (d • q) := by
    rw [← operator_spectral_integral A hA a b hbounds x hx,
      ← operator_spectral_integral A hA a b hbounds x hx]
    apply integral_mono_ae (continuous_integrable_probability ν (intervalCoordinate a b*q))
      (continuous_integrable_probability ν (d • q))
    filter_upwards [hae] with t ht
    exact mul_le_mul_of_nonneg_right ht.2 (hq t)
  simp only [_root_.map_smul,smul_eq_mul] at hlo hhi
  change c*‖polynomialVector A x p‖^2 ≤ ⟪polynomialVector A x p,A (polynomialVector A x p)⟫ ∧
    ⟪polynomialVector A x p,A (polynomialVector A x p)⟫ ≤ d*‖polynomialVector A x p‖^2
  rw [operator_polynomial_norm_moment A hA a b hbounds x hx,
    operator_polynomial_form_moment A hA a b hbounds x hx]
  constructor
  · have h := mul_le_mul_of_nonneg_left hlo (sq_nonneg ‖x‖)
    simpa only [mul_assoc,mul_left_comm] using h
  · have h := mul_le_mul_of_nonneg_left hhi (sq_nonneg ‖x‖)
    simpa only [mul_assoc,mul_left_comm] using h

/-- Any interval containing the actual initial spectral support yields the
sharp root upper bound for its entire BB trajectory. -/
theorem operator_support_interval_rootFactor_le (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (α₀ c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hsupport : operatorActiveSupport A hA a b hbounds (g 0) hg0 ⊆ Icc c d)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤ rate c d :=
  hilbert_active_subspace_rootFactor_le A hA (polynomialCyclicSpace A (g 0))
    (polynomial_cyclic_space_invariant A (g 0)) c d α₀ hc hcd
    (operator_cyclic_form_bounds_of_support A hA a b hbounds (g 0) hg0 c d hsupport)
    g hg0 (mem_polynomial_cyclic_space A (g 0)) hfirst hupdate

lemma operator_active_endpoints (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) :
    a ≤ sInf (operatorActiveSupport A hA a b hbounds x hx) ∧
    sInf (operatorActiveSupport A hA a b hbounds x hx) ≤
      sSup (operatorActiveSupport A hA a b hbounds x hx) ∧
    sSup (operatorActiveSupport A hA a b hbounds x hx) ≤ b := by
  have hs := operator_active_support_subset A hA a b hbounds x hx
  have hn := operator_active_support_nonempty A hA a b hbounds x hx
  have hlo : BddBelow (operatorActiveSupport A hA a b hbounds x hx) := ⟨a,fun _ ht => (hs ht).1⟩
  have hhi : BddAbove (operatorActiveSupport A hA a b hbounds x hx) := ⟨b,fun _ ht => (hs ht).2⟩
  exact ⟨le_csInf hn (fun _ ht => (hs ht).1),csInf_le_csSup hlo hhi hn,
    csSup_le hn (fun _ ht => (hs ht).2)⟩

lemma operator_active_endpoints_mem (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) :
    sInf (operatorActiveSupport A hA a b hbounds x hx) ∈ operatorActiveSupport A hA a b hbounds x hx ∧
    sSup (operatorActiveSupport A hA a b hbounds x hx) ∈ operatorActiveSupport A hA a b hbounds x hx := by
  have hs := operator_active_support_subset A hA a b hbounds x hx
  have hn := operator_active_support_nonempty A hA a b hbounds x hx
  have hc := (operator_active_support_isCompact A hA a b hbounds x hx).isClosed
  exact ⟨hc.csInf_mem hn ⟨a,fun _ ht => (hs ht).1⟩,
    hc.csSup_mem hn ⟨b,fun _ ht => (hs ht).2⟩⟩

/-- The manuscript's intrinsic active-endpoint upper rate, using the minimum
and maximum of the actual scalar spectral support of the initial gradient. -/
theorem operator_active_support_rootFactor_le (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (α₀ : ℝ)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    rootFactor (fun n => ‖g n‖/‖g 0‖) ≤
      rate (sInf (operatorActiveSupport A hA a b hbounds (g 0) hg0))
        (sSup (operatorActiveSupport A hA a b hbounds (g 0) hg0)) := by
  have hd := operator_active_endpoints A hA a b hbounds (g 0) hg0
  have hs := operator_active_support_subset A hA a b hbounds (g 0) hg0
  apply operator_support_interval_rootFactor_le A hA a b hbounds g hg0 α₀ _ _
    (ha.trans_le hd.1) hd.2.1 _ hfirst hupdate
  intro t ht
  exact ⟨csInf_le ⟨a,fun _ hr => (hs hr).1⟩ ht,
    le_csSup ⟨b,fun _ hr => (hs hr).2⟩ ht⟩

theorem operator_singleton_support_eigenvector (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) (ell : ℝ)
    (hsupport : operatorActiveSupport A hA a b hbounds x hx = {ell}) :
    A x = ell • x := by
  let p : ℝ[X] := Polynomial.X - Polynomial.C ell
  have hae : ∀ᵐ (t : Icc a b) ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)),
      (t:ℝ) = ell := by
    apply (ae_mem_measureSupport _).mono
    intro t ht
    have hm : (t:ℝ) ∈ operatorActiveSupport A hA a b hbounds x hx := ⟨t,ht,rfl⟩
    simpa only [hsupport,mem_singleton_iff] using hm
  have hz : (operatorMomentState A hA a b hbounds x hx).1
      ((p.toContinuousMapOn (Icc a b))^2) = 0 := by
    rw [← operator_spectral_integral A hA a b hbounds x hx]
    apply integral_eq_zero_of_ae
    filter_upwards [hae] with t ht
    simp [p,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap,ht]
  have hn := operator_polynomial_norm_moment A hA a b hbounds x hx p
  rw [hz,mul_zero] at hn
  have hp : polynomialVector A x p = A x - ell • x := by
    simp [polynomialVector,p,ContinuousLinearMap.sub_apply,ContinuousLinearMap.algebraMap_apply]
  rw [hp] at hn
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hn))

/-- A singleton intrinsic spectral support forces termination by the second
gradient, even when the first scalar step was chosen arbitrarily. -/
theorem operator_singleton_support_terminates (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (α₀ ell : ℝ)
    (hsupport : operatorActiveSupport A hA a b hbounds (g 0) hg0 = {ell})
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) : g 2 = 0 := by
  have hell : ell ∈ operatorActiveSupport A hA a b hbounds (g 0) hg0 := by
    rw [hsupport]
    exact mem_singleton ell
  have haell := (operator_active_support_subset A hA a b hbounds (g 0) hg0 hell).1
  exact single_eigenvalue_terminates A.toLinearMap ell α₀ (ha.trans_le haell) g hg0
    (operator_singleton_support_eigenvector A hA a b hbounds (g 0) hg0 ell hsupport) hfirst hupdate

lemma operator_active_rate_le_global (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (ha : 0 < a)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) :
    rate (sInf (operatorActiveSupport A hA a b hbounds x hx))
      (sSup (operatorActiveSupport A hA a b hbounds x hx)) ≤ rate a b := by
  have h := operator_active_endpoints A hA a b hbounds x hx
  exact rate_mono_interval ha h.1 h.2.1 h.2.2

end
end BB
