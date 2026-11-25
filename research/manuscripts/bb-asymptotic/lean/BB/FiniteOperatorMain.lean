import BB.FiniteMain
import BB.OperatorMoments
import BB.HilbertWeightedSharpness

/-!
# Exact finite-dimensional main statements for actual operator trajectories

The admissible sets quantify over vectors in the original inner-product space.
An orthonormal eigenbasis transports these sets exactly to the proved diagonal
sets. Fixed spectral weights are actual linear operators, rather than assumed
quotient identities.
-/

namespace BB
noncomputable section
open scoped BigOperators
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure IsOperatorDelayedTrajectory (H : E →ₗ[ℝ] E) (step : E → ℝ)
    (g : ℕ → E) (α₀ : ℝ) : Prop where
  initial_ne : g 0 ≠ 0
  firstStep_pos : 0 < α₀
  first : g 1 = operatorGradientStep H α₀ (g 0)
  update : ∀ n, g (n+2) = operatorGradientStep H (step (g n)) (g (n+1))

def operatorTrajectoryFactor (g : ℕ → E) : ℝ := rootFactor (fun n => ‖g n‖/‖g 0‖)

def operatorAttainableFactors (H : E →ₗ[ℝ] E) (step : E → ℝ) : Set ℝ :=
  {ρ | ∃ (g : ℕ → E) (α₀ : ℝ), IsOperatorDelayedTrajectory H step g α₀ ∧
    operatorTrajectoryFactor g = ρ}

def operatorMatchedUniformRates (H : E →ₗ[ℝ] E) (step : E → ℝ) : Set ℝ :=
  {γ | 0 < γ ∧ γ < 1 ∧ ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ → E),
    IsOperatorDelayedTrajectory H step g (step (g 0)) →
      ∀ n, ‖g n‖ ≤ C*γ^n*‖g 0‖}

lemma operator_delayed_trajectory_unique (H : E →ₗ[ℝ] E) (step : E → ℝ)
    (g v : ℕ → E) (h0 : g 0 = v 0) (h1 : g 1 = v 1)
    (hg : ∀ n, g (n+2) = operatorGradientStep H (step (g n)) (g (n+1)))
    (hv : ∀ n, v (n+2) = operatorGradientStep H (step (v n)) (v (n+1))) : g = v := by
  funext n
  exact @Nat.twoStepInduction (fun n => g n = v n) h0 h1
    (fun k hk hk1 => by change g (k+2) = v (k+2); rw [hg k,hv k,hk,hk1]) n

section Finite
variable [FiniteDimensional ℝ E]

lemma from_eigen_coordinates_eq_self {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (x : E) :
    fromEigenCoordinates hH (eigenCoordinates hH x) = x :=
  eigen_coordinates_injective hH (eigen_coordinates_from hH _)

lemma eigen_coordinates_add {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (x y : E) :
    eigenCoordinates hH (x+y) = eigenCoordinates hH x + eigenCoordinates hH y := by
  funext i
  exact congrArg (fun z => z i) (map_add (hH.eigenvectorBasis rfl).repr x y)

lemma eigen_coordinates_smul {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (c : ℝ) (x : E) :
    eigenCoordinates hH (c • x) = c • eigenCoordinates hH x := by
  funext i
  exact congrArg (fun z => z i) (map_smul (hH.eigenvectorBasis rfl).repr c x)

def finiteSpectralWeight {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ) : E →ₗ[ℝ] E where
  toFun x := fromEigenCoordinates hH (fun i => ψ i * eigenCoordinates hH x i)
  map_add' x y := by
    apply eigen_coordinates_injective hH
    rw [eigen_coordinates_add]
    simp only [eigen_coordinates_from,eigen_coordinates_add]
    funext i
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    apply eigen_coordinates_injective hH
    rw [eigen_coordinates_smul]
    simp only [eigen_coordinates_from,eigen_coordinates_smul]
    funext i
    simp only [Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

@[simp] lemma eigen_coordinates_spectral_weight {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ) (x : E) (i : Fin (FiniteDimensional.finrank ℝ E)) :
    eigenCoordinates hH (finiteSpectralWeight hH ψ x) i = ψ i * eigenCoordinates hH x i :=
  congrFun (eigen_coordinates_from hH _) i

lemma eigen_coordinates_weighted_quotient {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ) (x : E) :
    operatorWeightedBB H (finiteSpectralWeight hH ψ) x =
      weightedBB (eigenValues hH) ψ (eigenCoordinates hH x) := by
  unfold operatorWeightedBB weightedBB weightedEnergy
  rw [eigen_coordinates_inner_pair hH x,eigen_coordinates_inner_pair hH x]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro i _
  · rw [eigen_coordinates_spectral_weight]
    ring
  · rw [eigen_coordinates_spectral_weight,eigen_coordinates_apply]
    ring

lemma operator_trajectory_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (step : E → ℝ) (dstep : (Fin (FiniteDimensional.finrank ℝ E) → ℝ) → ℝ)
    (hstep : ∀ x, step x = dstep (eigenCoordinates hH x))
    (g : ℕ → E) (α₀ : ℝ) (hg : IsOperatorDelayedTrajectory H step g α₀) :
    IsDelayedTrajectory (eigenValues hH) dstep (fun n => eigenCoordinates hH (g n)) α₀ := by
  refine ⟨?_,hg.firstStep_pos,?_,?_⟩
  · rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg.initial_ne)
  · rw [hg.first,eigen_coordinates_update]
  · intro n
    rw [hg.update n,eigen_coordinates_update,hstep]

lemma diagonal_trajectory_from_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (step : E → ℝ) (dstep : (Fin (FiniteDimensional.finrank ℝ E) → ℝ) → ℝ)
    (hstep : ∀ x, step x = dstep (eigenCoordinates hH x))
    (v : ℕ → Fin (FiniteDimensional.finrank ℝ E) → ℝ) (α₀ : ℝ)
    (hv : IsDelayedTrajectory (eigenValues hH) dstep v α₀) :
    IsOperatorDelayedTrajectory H step (fun n => fromEigenCoordinates hH (v n)) α₀ := by
  refine ⟨?_,hv.firstStep_pos,?_,?_⟩
  · intro hz
    have hn := eigen_coordinates_energy hH (fromEigenCoordinates hH (v 0))
    rw [eigen_coordinates_from,hz,norm_zero,zero_pow (by decide : 2 ≠ 0)] at hn
    exact hv.initial_pos.ne' hn
  · apply eigen_coordinates_injective hH
    simpa only [eigen_coordinates_from,eigen_coordinates_update] using hv.first
  · intro n
    apply eigen_coordinates_injective hH
    rw [eigen_coordinates_from,eigen_coordinates_update,hstep,eigen_coordinates_from,eigen_coordinates_from]
    exact hv.update n

lemma operator_factor_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) (g : ℕ → E) :
    normalizedTrajectoryFactor (fun n => eigenCoordinates hH (g n)) = operatorTrajectoryFactor g := by
  simp only [normalizedTrajectoryFactor,operatorTrajectoryFactor,eigen_coordinates_norm]

lemma operator_factor_from_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (v : ℕ → Fin (FiniteDimensional.finrank ℝ E) → ℝ) :
    operatorTrajectoryFactor (fun n => fromEigenCoordinates hH (v n)) = normalizedTrajectoryFactor v := by
  rw [← operator_factor_coordinates hH]
  simp only [eigen_coordinates_from]

theorem operator_attainable_factors_eq_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (step : E → ℝ) (dstep : (Fin (FiniteDimensional.finrank ℝ E) → ℝ) → ℝ)
    (hstep : ∀ x, step x = dstep (eigenCoordinates hH x)) :
    operatorAttainableFactors H step = attainableFactors (eigenValues hH) dstep := by
  ext ρ
  constructor
  · rintro ⟨g,α₀,hg,hρ⟩
    exact ⟨fun n => eigenCoordinates hH (g n),α₀,
      operator_trajectory_coordinates hH step dstep hstep g α₀ hg,
      (operator_factor_coordinates hH g).trans hρ⟩
  · rintro ⟨v,α₀,hv,hρ⟩
    exact ⟨fun n => fromEigenCoordinates hH (v n),α₀,
      diagonal_trajectory_from_coordinates hH step dstep hstep v α₀ hv,
      (operator_factor_from_coordinates hH v).trans hρ⟩

theorem operator_uniform_rates_eq_coordinates {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (step : E → ℝ) (dstep : (Fin (FiniteDimensional.finrank ℝ E) → ℝ) → ℝ)
    (hstep : ∀ x, step x = dstep (eigenCoordinates hH x)) :
    operatorMatchedUniformRates H step = matchedUniformRates (eigenValues hH) dstep := by
  ext γ
  constructor
  · rintro ⟨hγ0,hγ1,C,hC,hall⟩
    refine ⟨hγ0,hγ1,C,hC,?_⟩
    intro v hv n
    have hg := diagonal_trajectory_from_coordinates hH step dstep hstep v _ hv
    have hs : step (fromEigenCoordinates hH (v 0)) = dstep (v 0) := by
      rw [hstep,eigen_coordinates_from]
    rw [← hs] at hg
    have he := hall (fun n => fromEigenCoordinates hH (v n)) hg n
    simpa only [← eigen_coordinates_norm hH, eigen_coordinates_from] using he
  · rintro ⟨hγ0,hγ1,C,hC,hall⟩
    refine ⟨hγ0,hγ1,C,hC,?_⟩
    intro g hg n
    have hv := operator_trajectory_coordinates hH step dstep hstep g _ hg
    rw [hstep] at hv
    simpa only [eigen_coordinates_norm] using hall (fun n => eigenCoordinates hH (g n)) hv n

theorem finite_operator_bb1_isGreatest {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    IsGreatest (operatorAttainableFactors H (operatorBB1 H)) (rate a b) := by
  rw [operator_attainable_factors_eq_coordinates hH _ _ (eigen_coordinates_quotient hH)]
  exact finite_bb1_isGreatest (eigenValues hH) lo hi a b ha hab hlo hhi hbounds

theorem finite_operator_bb1_supremum {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    sSup (operatorAttainableFactors H (operatorBB1 H)) = rate a b :=
  (finite_operator_bb1_isGreatest hH lo hi a b ha hab hlo hhi hbounds).csSup_eq

theorem finite_operator_bb1_uniform_isGLB {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    IsGLB (operatorMatchedUniformRates H (operatorBB1 H)) (rate a b) := by
  rw [operator_uniform_rates_eq_coordinates hH _ _ (eigen_coordinates_quotient hH)]
  have hq : weightedBB (eigenValues hH) (fun _ => 1) = diagonalBB1 (eigenValues hH) :=
    funext (weighted_bb_one _)
  simpa only [hq] using finite_weighted_uniform_isGLB (eigenValues hH) (fun _ => 1)
    lo hi a b ha hab hlo hhi hbounds (fun _ => zero_lt_one)

theorem finite_operator_bb1_uniform_infimum {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) :
    sInf (operatorMatchedUniformRates H (operatorBB1 H)) = rate a b := by
  rw [operator_uniform_rates_eq_coordinates hH _ _ (eigen_coordinates_quotient hH)]
  exact finite_bb1_uniform_rate_infimum (eigenValues hH) lo hi a b ha hab hlo hhi hbounds

theorem finite_operator_weighted_isGreatest {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    IsGreatest (operatorAttainableFactors H (operatorWeightedBB H (finiteSpectralWeight hH ψ)))
      (rate a b) := by
  rw [operator_attainable_factors_eq_coordinates hH _ _ (eigen_coordinates_weighted_quotient hH ψ)]
  exact finite_weighted_isGreatest (eigenValues hH) ψ lo hi a b ha hab hlo hhi hbounds hψ

theorem finite_operator_weighted_active_rootFactor_le {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ) (a b α₀ : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hψ : ∀ i, 0 < ψ i)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hactive : ∀ i, eigenCoordinates hH (g 0) i ≠ 0 →
      a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b)
    (hfirst : g 1 = operatorGradientStep H α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H
      (operatorWeightedBB H (finiteSpectralWeight hH ψ) (g n)) (g (n+1))) :
    operatorTrajectoryFactor g ≤ rate a b := by
  have hv0 : 0 < energy (eigenCoordinates hH (g 0)) := by
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg0)
  have hvfirst : eigenCoordinates hH (g 1) =
      gradientUpdate (eigenValues hH) α₀ (eigenCoordinates hH (g 0)) := by
    rw [hfirst,eigen_coordinates_update]
  have hvupdate : ∀ n, eigenCoordinates hH (g (n+2)) =
      gradientUpdate (eigenValues hH) (weightedBB (eigenValues hH) ψ (eigenCoordinates hH (g n)))
        (eigenCoordinates hH (g (n+1))) := by
    intro n
    rw [hupdate n,eigen_coordinates_update,eigen_coordinates_weighted_quotient]
  simpa only [eigen_coordinates_norm,operatorTrajectoryFactor] using
    weighted_gradient_active_rootFactor_le (eigenValues hH) ψ a b α₀ ha hab hψ
      (fun n => eigenCoordinates hH (g n)) hv0 hactive hvfirst hvupdate

theorem finite_operator_weighted_supremum {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    sSup (operatorAttainableFactors H (operatorWeightedBB H (finiteSpectralWeight hH ψ))) =
      rate a b :=
  (finite_operator_weighted_isGreatest hH ψ lo hi a b ha hab hlo hhi hbounds hψ).csSup_eq

theorem finite_operator_weighted_uniform_isGLB {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    IsGLB (operatorMatchedUniformRates H (operatorWeightedBB H (finiteSpectralWeight hH ψ)))
      (rate a b) := by
  rw [operator_uniform_rates_eq_coordinates hH _ _ (eigen_coordinates_weighted_quotient hH ψ)]
  exact finite_weighted_uniform_isGLB (eigenValues hH) ψ lo hi a b ha hab hlo hhi hbounds hψ

theorem finite_operator_weighted_uniform_infimum {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (ψ : Fin (FiniteDimensional.finrank ℝ E) → ℝ)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E)) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlo : eigenValues hH lo = a) (hhi : eigenValues hH hi = b)
    (hbounds : ∀ i, a ≤ eigenValues hH i ∧ eigenValues hH i ≤ b) (hψ : ∀ i, 0 < ψ i) :
    sInf (operatorMatchedUniformRates H (operatorWeightedBB H (finiteSpectralWeight hH ψ))) =
      rate a b := by
  rw [operator_uniform_rates_eq_coordinates hH _ _ (eigen_coordinates_weighted_quotient hH ψ)]
  exact finite_weighted_uniform_rate_infimum (eigenValues hH) ψ lo hi a b ha hab hlo hhi hbounds hψ

theorem eigen_values_range_eq_spectrum {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) :
    Set.range (eigenValues hH) = spectrum ℝ H := by
  ext ell
  constructor
  · rintro ⟨i,rfl⟩
    exact (hH.hasEigenvalue_eigenvalues rfl i).mem_spectrum
  · intro hell
    obtain ⟨x,hx⟩ := (Module.End.HasEigenvalue.of_mem_spectrum hell).exists_hasEigenvector
    have hi : ∃ i, eigenCoordinates hH x i ≠ 0 := by
      by_contra hn
      push_neg at hn
      have he : eigenCoordinates hH x = eigenCoordinates hH 0 := by
        funext i
        rw [hn i]
        simp only [eigenCoordinates,map_zero,PiLp.zero_apply]
      exact hx.2 (eigen_coordinates_injective hH he)
    obtain ⟨i,hi⟩ := hi
    refine ⟨i,?_⟩
    have he := congrArg (fun y => eigenCoordinates hH y i) hx.apply_eq_smul
    change eigenCoordinates hH (H x) i = eigenCoordinates hH (ell • x) i at he
    rw [eigen_coordinates_apply,eigen_coordinates_smul] at he
    exact mul_right_cancel₀ hi he

lemma eigen_extremes_are_spectral_extremes {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Fin (FiniteDimensional.finrank ℝ E))
    (hbounds : ∀ i, eigenValues hH lo ≤ eigenValues hH i ∧ eigenValues hH i ≤ eigenValues hH hi) :
    IsLeast (spectrum ℝ H) (eigenValues hH lo) ∧
      IsGreatest (spectrum ℝ H) (eigenValues hH hi) := by
  rw [← eigen_values_range_eq_spectrum hH]
  exact ⟨⟨⟨lo,rfl⟩,by rintro _ ⟨i,rfl⟩; exact (hbounds i).1⟩,
    ⟨⟨hi,rfl⟩,by rintro _ ⟨i,rfl⟩; exact (hbounds i).2⟩⟩

/-- Canonical operator BB1 main theorem with the endpoints proved to be the
actual minimum and maximum of the real spectrum. The scalar case is included. -/
theorem finite_operator_bb1_main [Nontrivial E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (m M : ℝ) (hm : 0 < m)
    (hform : ∀ x : E, m*‖x‖^2 ≤ ⟪x,H x⟫ ∧ ⟪x,H x⟫ ≤ M*‖x‖^2) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ IsLeast (spectrum ℝ H) a ∧ IsGreatest (spectrum ℝ H) b ∧
      IsGreatest (operatorAttainableFactors H (operatorBB1 H)) (rate a b) ∧
      sSup (operatorAttainableFactors H (operatorBB1 H)) = rate a b ∧
      sInf (operatorMatchedUniformRates H (operatorBB1 H)) = rate a b := by
  letI : Nonempty (Fin (FiniteDimensional.finrank ℝ E)) :=
    ⟨⟨0,FiniteDimensional.finrank_pos⟩⟩
  obtain ⟨lo,hi,hbounds⟩ := finite_extreme_indices (eigenValues hH)
  have ha : 0 < eigenValues hH lo := hm.trans_le (eigenvalue_bounds hH m M hform lo).1
  have hab := (hbounds hi).1
  obtain ⟨hl,hu⟩ := eigen_extremes_are_spectral_extremes hH lo hi hbounds
  exact ⟨_,_,ha,hab,hl,hu,
    finite_operator_bb1_isGreatest hH lo hi _ _ ha hab rfl rfl hbounds,
    finite_operator_bb1_supremum hH lo hi _ _ ha hab rfl rfl hbounds,
    finite_operator_bb1_uniform_infimum hH lo hi _ _ ha hab rfl rfl hbounds⟩

theorem finite_operator_weighted_main [Nontrivial E] {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (m M : ℝ) (hm : 0 < m)
    (hform : ∀ x : E, m*‖x‖^2 ≤ ⟪x,H x⟫ ∧ ⟪x,H x⟫ ≤ M*‖x‖^2)
    (Ψ : ℝ → ℝ) (hΨ : ∀ ell ∈ spectrum ℝ H, 0 < Ψ ell) :
    let W := finiteSpectralWeight hH (fun i => Ψ (eigenValues hH i))
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ IsLeast (spectrum ℝ H) a ∧ IsGreatest (spectrum ℝ H) b ∧
      IsGreatest (operatorAttainableFactors H (operatorWeightedBB H W)) (rate a b) ∧
      sSup (operatorAttainableFactors H (operatorWeightedBB H W)) = rate a b ∧
      sInf (operatorMatchedUniformRates H (operatorWeightedBB H W)) = rate a b := by
  dsimp only
  letI : Nonempty (Fin (FiniteDimensional.finrank ℝ E)) :=
    ⟨⟨0,FiniteDimensional.finrank_pos⟩⟩
  obtain ⟨lo,hi,hbounds⟩ := finite_extreme_indices (eigenValues hH)
  have ha : 0 < eigenValues hH lo := hm.trans_le (eigenvalue_bounds hH m M hform lo).1
  have hab := (hbounds hi).1
  have hψ : ∀ i, 0 < Ψ (eigenValues hH i) :=
    fun i => hΨ _ ((hH.hasEigenvalue_eigenvalues rfl i).mem_spectrum)
  obtain ⟨hl,hu⟩ := eigen_extremes_are_spectral_extremes hH lo hi hbounds
  exact ⟨_,_,ha,hab,hl,hu,
    finite_operator_weighted_isGreatest hH _ lo hi _ _ ha hab rfl rfl hbounds hψ,
    finite_operator_weighted_supremum hH _ lo hi _ _ ha hab rfl rfl hbounds hψ,
    finite_operator_weighted_uniform_infimum hH _ lo hi _ _ ha hab rfl rfl hbounds hψ⟩

end Finite
end
end BB
