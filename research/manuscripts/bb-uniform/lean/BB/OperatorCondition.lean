import BB.OperatorBridge

set_option autoImplicit false

noncomputable section
namespace BB.Operator
open Module.End
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The standard Rayleigh expansion follows from the actual spectral isometry. -/
theorem quadratic_form_spectral {W : V →ₗ[ℝ] V} (hW : W.IsSymmetric) (x : V) :
    @inner ℝ _ _ x (W x) = ∑ μ : Eigenvalues W, (μ:ℝ)*‖coordinates hW x μ‖^2 := by
  have hh := moment_inner_decomposition (W := (LinearMap.id : V →ₗ[ℝ] V)) hW (fun x => rfl) x
  simpa only [LinearMap.id_apply,real_inner_self_eq_norm_sq,Submodule.coe_norm] using hh

/-- Bounds on every eigenvalue imply the corresponding global quadratic-form bounds. -/
theorem quadratic_bounds_of_spectral_bounds {W : V →ₗ[ℝ] V} (hW : W.IsSymmetric)
    {m M : ℝ} (hs : ∀ μ : Eigenvalues W, m ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ M) :
    ∀ x : V, m*‖x‖^2 ≤ @inner ℝ _ _ x (W x) ∧ @inner ℝ _ _ x (W x) ≤ M*‖x‖^2 := by
  intro x
  rw [quadratic_form_spectral hW,← coordinates_sq_norm hW x]
  constructor
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun μ _ => mul_le_mul_of_nonneg_right (hs μ).1 (sq_nonneg _))
  · rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun μ _ => mul_le_mul_of_nonneg_right (hs μ).2 (sq_nonneg _))

/-- Conversely, global quadratic-form bounds constrain every actual eigenvalue. -/
theorem spectral_bounds_of_quadratic_bounds {W : V →ₗ[ℝ] V} {m M : ℝ}
    (hq : ∀ x : V, m*‖x‖^2 ≤ @inner ℝ _ _ x (W x) ∧ @inner ℝ _ _ x (W x) ≤ M*‖x‖^2) :
    ∀ μ : Eigenvalues W, m ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ M := by
  intro μ
  obtain ⟨x,hx⟩ := μ.property.exists_hasEigenvector
  have hh := hq x
  rw [hx.apply_eq_smul,inner_smul_right,real_inner_self_eq_norm_sq] at hh
  have hn : 0 < ‖x‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hx.2)
  exact ⟨(mul_le_mul_right hn).mp hh.1,(mul_le_mul_right hn).mp hh.2⟩

/-- A nontrivial finite-dimensional symmetric operator has an eigenvalue. -/
theorem eigenvalues_nonempty [Nontrivial V] {W : V →ₗ[ℝ] V} (hW : W.IsSymmetric) :
    Nonempty (Eigenvalues W) := by
  have hn : 0 < FiniteDimensional.finrank ℝ V := FiniteDimensional.finrank_pos
  let i : Fin (FiniteDimensional.finrank ℝ V) := ⟨0,hn⟩
  exact ⟨⟨hW.eigenvalues rfl i,hW.hasEigenvalue_eigenvalues rfl i⟩⟩

def spectralMin (W : V →ₗ[ℝ] V) [Nonempty (Eigenvalues W)] : ℝ :=
  (Finset.univ.min' Finset.univ_nonempty : Eigenvalues W)

def spectralMax (W : V →ₗ[ℝ] V) [Nonempty (Eigenvalues W)] : ℝ :=
  (Finset.univ.max' Finset.univ_nonempty : Eigenvalues W)

/-- The SPD spectral condition number, as used in the manuscript. -/
def spectralConditionNumber (W : V →ₗ[ℝ] V) [Nonempty (Eigenvalues W)] : ℝ :=
  spectralMax W / spectralMin W

theorem spectralMin_le (W : V →ₗ[ℝ] V) [Nonempty (Eigenvalues W)] (μ : Eigenvalues W) :
    spectralMin W ≤ (μ:ℝ) := Finset.min'_le _ _ (Finset.mem_univ μ)

theorem le_spectralMax (W : V →ₗ[ℝ] V) [Nonempty (Eigenvalues W)] (μ : Eigenvalues W) :
    (μ:ℝ) ≤ spectralMax W := Finset.le_max' _ _ (Finset.mem_univ μ)

theorem spectralMin_pos {W : V →ₗ[ℝ] V} [Nonempty (Eigenvalues W)]
    (hpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (W x)) : 0 < spectralMin W :=
  eigenvalue_pos hpd (Finset.univ.min' Finset.univ_nonempty)

/-- The condition-number bound yields the exact normalized energy hypotheses. -/
theorem energy_bounds_of_condition {W : V →ₗ[ℝ] V} [Nonempty (Eigenvalues W)]
    (hW : W.IsSymmetric) (hpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {χ : ℝ} (hcond : spectralConditionNumber W ≤ χ) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : V,
      m*‖x‖^2 ≤ @inner ℝ _ _ x (W x) ∧ @inner ℝ _ _ x (W x) ≤ (χ*m)*‖x‖^2 := by
  have hm := spectralMin_pos hpd
  have hmax : spectralMax W ≤ χ*spectralMin W := (div_le_iff hm).mp hcond
  refine ⟨spectralMin W,hm,quadratic_bounds_of_spectral_bounds hW ?_⟩
  intro μ
  exact ⟨spectralMin_le W μ,(le_spectralMax W μ).trans hmax⟩

/-- Exact equivalence between the SPD condition bound and a positive coercivity scale. -/
theorem condition_iff_energy_bounds {W : V →ₗ[ℝ] V} [Nonempty (Eigenvalues W)]
    (hW : W.IsSymmetric) (hpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {χ : ℝ} (hχ : 0 ≤ χ) :
    spectralConditionNumber W ≤ χ ↔
      ∃ m : ℝ, 0 < m ∧ ∀ x : V,
        m*‖x‖^2 ≤ @inner ℝ _ _ x (W x) ∧ @inner ℝ _ _ x (W x) ≤ (χ*m)*‖x‖^2 := by
  constructor
  · exact energy_bounds_of_condition hW hpd
  · rintro ⟨m,hm,hq⟩
    have hs := spectral_bounds_of_quadratic_bounds hq
    have hlo : m ≤ spectralMin W := (hs (Finset.univ.min' Finset.univ_nonempty)).1
    have hhi : spectralMax W ≤ χ*m := (hs (Finset.univ.max' Finset.univ_nonempty)).2
    apply (div_le_iff (spectralMin_pos hpd)).mpr
    exact hhi.trans (mul_le_mul_of_nonneg_left hlo hχ)

end BB.Operator
