import BB.OperatorActiveSupport

/-!
# The scalar spectral measures are supported on the actual spectrum

A resolvent inverse gives a norm gap. Polynomial moment identities transfer it
to the scalar measure; polynomial density then permits a continuous bump in the
gap. This proves support containment without assuming a spectral theorem for
projection-valued measures.
-/

namespace BB
noncomputable section
open MeasureTheory Set Filter
open scoped Polynomial Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma resolvent_norm_gap (A : E →L[ℝ] E) (ell : ℝ) (hell : ell ∉ spectrum ℝ A) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ y : E, δ*‖y‖ ≤ ‖ell • y-A y‖ := by
  have hu : IsUnit (algebraMap ℝ (E →L[ℝ] E) ell-A) := by
    by_contra hn
    exact hell (spectrum.mem_iff.mpr hn)
  obtain ⟨u,hu⟩ := hu
  let R : E →L[ℝ] E := ↑(u⁻¹)
  have hR : 0 < ‖R‖+1 := by positivity
  refine ⟨(‖R‖+1)⁻¹,inv_pos.mpr hR,?_⟩
  intro y
  have hrecover : R (ell • y-A y) = y := by
    change R ((algebraMap ℝ (E →L[ℝ] E) ell-A) y) = y
    rw [← hu]
    change (↑(u⁻¹) : E →L[ℝ] E) ((u : E →L[ℝ] E) y) = y
    rw [← ContinuousLinearMap.mul_apply,Units.inv_mul,ContinuousLinearMap.one_apply]
  have hn := R.le_opNorm (ell • y-A y)
  rw [hrecover] at hn
  rw [← div_eq_inv_mul]
  apply (div_le_iff hR).mpr
  nlinarith [norm_nonneg (ell • y-A y)]

lemma operator_moment_polynomial_gap (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) (ell δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ y : E, δ*‖y‖ ≤ ‖ell • y-A y‖) (p : ℝ[X]) :
    δ^2 * (operatorMomentState A hA a b hbounds x hx).1
      ((p.toContinuousMapOn (Icc a b))^2) ≤
      (operatorMomentState A hA a b hbounds x hx).1
        ((ContinuousMap.const (Icc a b) ell-intervalCoordinate a b)^2 *
          (p.toContinuousMapOn (Icc a b))^2) := by
  let v := polynomialVector A x p
  let q : ℝ[X] := (Polynomial.C ell-Polynomial.X)*p
  have hq : polynomialVector A x q = ell • v-A v := by
    simp only [q,v,polynomialVector,map_mul,map_sub,Polynomial.aeval_C,Polynomial.aeval_X,
      ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,ContinuousLinearMap.algebraMap_apply]
  have he : (q.toContinuousMapOn (Icc a b))^2 =
      (ContinuousMap.const (Icc a b) ell-intervalCoordinate a b)^2 *
        (p.toContinuousMapOn (Icc a b))^2 := by
    ext t
    simp only [q,Polynomial.toContinuousMapOn,Polynomial.toContinuousMap,ContinuousMap.coe_mk,
      ContinuousMap.pow_apply,ContinuousMap.mul_apply,ContinuousMap.sub_apply,
      ContinuousMap.const_apply,Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_C,
      Polynomial.eval_X,intervalCoordinate]
    ring
  have hs : δ^2*‖v‖^2 ≤ ‖ell • v-A v‖^2 := by
    have h := hgap v
    have hh := mul_self_le_mul_self (mul_nonneg hδ.le (norm_nonneg v)) h
    nlinarith [hh]
  rw [← hq,operator_polynomial_norm_moment A hA a b hbounds x hx q,he] at hs
  change δ^2*‖polynomialVector A x p‖^2 ≤ _ at hs
  rw [operator_polynomial_norm_moment A hA a b hbounds x hx p] at hs
  apply (mul_le_mul_left (sq_pos_of_pos (norm_pos_iff.mpr hx))).mp
  simpa only [mul_assoc,mul_left_comm] using hs

lemma operator_moment_continuous_gap (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) (ell δ : ℝ) (hδ : 0 < δ)
    (hgap : ∀ y : E, δ*‖y‖ ≤ ‖ell • y-A y‖) (f : C(Icc a b,ℝ)) :
    δ^2 * (operatorMomentState A hA a b hbounds x hx).1 (f^2) ≤
      (operatorMomentState A hA a b hbounds x hx).1
        ((ContinuousMap.const (Icc a b) ell-intervalCoordinate a b)^2 * f^2) := by
  let L := operatorMomentState A hA a b hbounds x hx
  let q := (ContinuousMap.const (Icc a b) ell-intervalCoordinate a b)^2
  let S : Set C(Icc a b,ℝ) := {f | δ^2*L.1 (f^2) ≤ L.1 (q*f^2)}
  have hL : Continuous (fun f : C(Icc a b,ℝ) => L.1 f) := (WeakDual.toNormedDual L.1).continuous
  have hS : IsClosed S := isClosed_le
    (continuous_const.mul (hL.comp (continuous_id.pow 2)))
    (hL.comp (continuous_const.mul (continuous_id.pow 2)))
  have hp : (polynomialFunctions (Icc a b) : Set C(Icc a b,ℝ)) ⊆ S := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨p,rfl⟩ := hf
    exact operator_moment_polynomial_gap A hA a b hbounds x hx ell δ hδ hgap p
  exact (closure_minimal hp hS) (continuousMap_mem_polynomialFunctions_closure a b f)

theorem operator_active_support_subset_spectrum (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) :
    operatorActiveSupport A hA a b hbounds x hx ⊆ spectrum ℝ A := by
  rintro ell ⟨t,ht,rfl⟩
  by_contra hell
  obtain ⟨δ,hδ,hgap⟩ := resolvent_norm_gap A (t:ℝ) hell
  let L := operatorMomentState A hA a b hbounds x hx
  let ν := operatorSpectralProbability A hA a b hbounds x hx
  let q : C(Icc a b,ℝ) := (ContinuousMap.const (Icc a b) (t:ℝ)-intervalCoordinate a b)^2
  let m : C(Icc a b,ℝ) := ContinuousMap.const (Icc a b) (δ^2)-q
  let f : C(Icc a b,ℝ) := ⟨fun s => max 0 (m s),continuous_const.max m.continuous⟩
  have hf : ∀ s, 0 ≤ f s := fun s => le_max_left _ _
  have hgapf : δ^2*L.1 (f^2) ≤ L.1 (q*f^2) :=
    operator_moment_continuous_gap A hA a b hbounds x hx (t:ℝ) δ hδ hgap f
  have he : m*f^2 = f^3 := by
    ext s
    by_cases hm : 0 ≤ m s
    · simp only [ContinuousMap.mul_apply,ContinuousMap.pow_apply,f,ContinuousMap.coe_mk,max_eq_right hm]
      ring
    · simp only [ContinuousMap.mul_apply,ContinuousMap.pow_apply,f,ContinuousMap.coe_mk,
        max_eq_left (le_of_not_ge hm),zero_pow (by decide : 2 ≠ 0),
        zero_pow (by decide : 3 ≠ 0),mul_zero]
  have he' : m*f^2 = δ^2 • f^2-q*f^2 := by
    ext s
    simp only [m,ContinuousMap.mul_apply,ContinuousMap.pow_apply,ContinuousMap.sub_apply,
      ContinuousMap.smul_apply,ContinuousMap.const_apply,smul_eq_mul]
    ring
  have hz : L.1 (f^3) = 0 := by
    have hle : L.1 (f^3) ≤ 0 := by
      rw [← he,he',map_sub,_root_.map_smul,smul_eq_mul]
      exact sub_nonpos.mpr hgapf
    exact le_antisymm hle (L.2.1 _ (fun s => pow_nonneg (hf s) 3))
  have hint : (∫ s, ((f^3 : C(Icc a b,ℝ))) s ∂(ν : Measure (Icc a b))) = 0 := by
    rw [operator_spectral_integral]
    exact hz
  have hnonneg : ∀ s, 0 ≤ (f^3 : C(Icc a b,ℝ)) s := by
    intro s
    exact pow_nonneg (hf s) 3
  have hae : ∀ᵐ s ∂(ν : Measure (Icc a b)), (f^3 : C(Icc a b,ℝ)) s = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (eventually_of_forall hnonneg)
      (continuous_integrable_probability ν (f^3))).mp hint
  let U : Set (Icc a b) := {s | 0 < m s}
  have hU : IsOpen U := isOpen_lt continuous_const m.continuous
  have htU : t ∈ U := by
    change 0 < δ^2-((t:ℝ)-(t:ℝ))^2
    simpa only [sub_self,zero_pow (by decide : 2 ≠ 0),sub_zero] using sq_pos_of_pos hδ
  have hzero : (ν : Measure (Icc a b)) U = 0 := by
    have hnot : ∀ᵐ s ∂(ν : Measure (Icc a b)), s ∉ U := by
      filter_upwards [hae] with s hs
      intro hsU
      have hsf : 0 < f s := by
        change 0 < max 0 (m s)
        exact (lt_max_iff.mpr (Or.inr hsU))
      exact (pow_pos hsf 3).ne' hs
    simpa only [not_not] using ae_iff.mp hnot
  exact ht U hU htU hzero

theorem operator_spectral_probability_ae_mem_spectrum (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) :
    ∀ᵐ (t : Icc a b) ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)),
      (t:ℝ) ∈ spectrum ℝ A := by
  apply (ae_mem_measureSupport _).mono
  intro t ht
  exact operator_active_support_subset_spectrum A hA a b hbounds x hx ⟨t,ht,rfl⟩

theorem operator_spectral_measure_support_subset_spectrum (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2) (x : E) :
    Subtype.val '' measureSupport (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) ⊆
      spectrum ℝ A := by
  rintro ell ⟨t,ht,rfl⟩
  by_cases hx : x = 0
  · subst x
    have h := ht univ isOpen_univ (mem_univ t)
    simp only [operator_spectral_measure_zero,FiniteMeasure.toMeasure_zero] at h
    simp at h
  · have habs : (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) ≪
        (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)) := by
      intro S hS
      rw [operator_spectral_measure_nonzero A hA a b hbounds x hx,Measure.smul_apply,hS]
      simp
    exact operator_active_support_subset_spectrum A hA a b hbounds x hx
      ⟨t,measureSupport_subset_of_absolutelyContinuous habs ht,rfl⟩

theorem operator_spectral_measure_ae_mem_spectrum (A : E →L[ℝ] E)
    (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
    (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2) (x : E) :
    ∀ᵐ (t : Icc a b) ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)),
      (t:ℝ) ∈ spectrum ℝ A := by
  apply (ae_mem_measureSupport _).mono
  intro t ht
  exact operator_spectral_measure_support_subset_spectrum A hA a b hbounds x ⟨t,ht,rfl⟩

end
end BB
