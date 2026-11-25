import BB.MainTheorem
import BB.IntervalOperator
import BB.FrozenMap
import BB.OperatorLipschitz

/-! # One common certificate for the complete actual BB1--BB2 interval -/

set_option autoImplicit false
noncomputable section
namespace BB.Operator

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Both endpoints and every convex interpolation obey the true spectral step interval. -/
theorem frozen_interval_bounds (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H.toLinearMap, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (η : Set.Icc (0:ℝ) 1) {u : E} (hu : u ≠ 0) :
    1/b ≤ BB.Secant.blend η.1 u (H u) ∧ BB.Secant.blend η.1 u (H u) ≤ 1/a := by
  have hQ := quadratic_bounds_of_spectral_bounds hH hspec
  have hb := weightedAlpha_bounds hH (intervalWeight_commutes H.toLinearMap η.1 u)
    (intervalWeight_posDef ha hab η.2.1 η.2.2 hQ u) ha hab hspec hu
  rwa [intervalWeight_alpha hH ha (fun x => (hQ x).1)] at hb

/-- Actual cone invariance for the frozen secant family. -/
theorem frozen_interval_cone (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H.toLinearMap, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hM : b/a-1 ≤ M) (η : Set.Icc (0:ℝ) 1) {z : E × E}
    (hz : z ∈ BB.Local.pairCone M) : BB.Local.frozenMap H η z ∈ BB.Local.pairCone M := by
  by_cases hu : z.1 = 0
  · have hv : z.2 = 0 := by
      have hc : ‖z.2‖ ≤ M*‖z.1‖ := hz
      rw [hu,norm_zero,mul_zero] at hc
      exact norm_eq_zero.mp (le_antisymm hc (norm_nonneg _))
    have hz0 : z = 0 := Prod.ext hu hv
    rw [hz0,BB.Local.frozenMap_zero]
    exact BB.Local.zero_mem_pairCone M
  · have hs := frozen_interval_bounds H hH ha hab hspec η hu
    exact (spectral_step_norm_bound hH ha hab hspec hs.1 hs.2 z.2).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg z.2))

/-- The original interval family, including state-dependent and discontinuous
choices, has a common Lipschitz homogeneous certificate at the exact factor. -/
theorem frozen_interval_certificate (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {n : ℕ} (hn : Fintype.card (Eigenvalues H.toLinearMap) = n+2)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {M : ℝ} (hM : 0 ≤ M) :
    Nonempty (BB.Gluing.Certificate (BB.Local.frozenMap H) (BB.Local.pairCone M)
      (BB.endpointRate (sortedLambda H.toLinearMap hn 0)
        (sortedLambda H.toLinearMap hn (Fin.last (n+1))))) := by
  let a := sortedLambda H.toLinearMap hn 0
  let b := sortedLambda H.toLinearMap hn (Fin.last (n+1))
  have ha : 0 < a := sortedLambda_pos hn hpd 0
  have hab : a ≤ b := (sortedLambda_strictMono H.toLinearMap hn).monotone (Fin.zero_le _)
  have hQ : ∀ x : E, a*‖x‖^2 ≤ @inner ℝ _ _ x (H x) ∧
      @inner ℝ _ _ x (H x) ≤ b*‖x‖^2 :=
    quadratic_bounds_of_spectral_bounds hH (sorted_spectral_bounds H.toLinearMap hn)
  have hlo := fun x => (hQ x).1
  have hχ : 1 ≤ b/a := (one_le_div ha).mpr hab
  let Ω := Set.Icc (0:ℝ) 1 × E
  let W : Ω → E →ₗ[ℝ] E := fun ω => intervalWeight H.toLinearMap ω.1.1 ω.2
  let m : Ω → ℝ := fun ω => intervalScale H.toLinearMap a ω.1.1 ω.2
  have hm : ∀ ω : Ω, 0 < m ω := fun ω =>
    intervalScale_pos ha ω.1.2.1 ω.1.2.2 hlo ω.2
  have henergy : ∀ ω : Ω, ∀ x : E,
      m ω*‖x‖^2 ≤ @inner ℝ _ _ x (W ω x) ∧
      @inner ℝ _ _ x (W ω x) ≤ ((b/a)*m ω)*‖x‖^2 := fun ω =>
    intervalWeight_energy_bounds ha hab ω.1.2.1 ω.1.2.2 hQ ω.2
  obtain ⟨v⟩ := uniform_operator_sup_certificate hH hn hpd hχ hM W
    (fun ω => intervalWeight_commutes H.toLinearMap ω.1.1 ω.2) m hm
    (fun ω x => (henergy ω x).1) (fun ω x => (henergy ω x).2)
  refine ⟨{
    value := v.value
    prefactor := v.prefactor
    lipConstant := v.lipConstant
    prefactor_ge_one := v.prefactor_ge_one
    lipConstant_nonneg := v.lipConstant_nonneg
    lower := v.lower
    upper := v.upper
    lipschitz := v.lipschitz
    homogeneous := v.homogeneous
    decrease := ?_
  }⟩
  intro η z hz
  change v.value (BB.Local.frozenMap H η z) ≤ _
  have heq : stateMap H.toLinearMap (W (η,z.1)) z = BB.Local.frozenMap H η z :=
    intervalWeight_stateMap hH ha hlo η.1 z
  rw [← heq]
  exact v.decrease (η,z.1) z hz

/-- Uniform rate for arbitrary selections from the interval at every iteration. -/
theorem frozen_interval_uniform_rate (H : E →L[ℝ] E) (hH : H.toLinearMap.IsSymmetric)
    {n : ℕ} (hn : Fintype.card (Eigenvalues H.toLinearMap) = n+2)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {M : ℝ} (hM0 : 0 ≤ M)
    (hM : sortedLambda H.toLinearMap hn (Fin.last (n+1))/sortedLambda H.toLinearMap hn 0-1 ≤ M) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (η : ℕ → Set.Icc (0:ℝ) 1) (z : ℕ → E × E),
      z 0 ∈ BB.Local.pairCone M →
      (∀ k, z (k+1) = BB.Local.frozenMap H (η k) (z k)) → ∀ k,
      ‖z k‖ ≤ K*(BB.endpointRate (sortedLambda H.toLinearMap hn 0)
        (sortedLambda H.toLinearMap hn (Fin.last (n+1))))^k*‖z 0‖ := by
  obtain ⟨v⟩ := frozen_interval_certificate H hH hn hpd hM0
  refine ⟨v.prefactor,v.prefactor_ge_one,?_⟩
  intro η z hz hrec k
  have ha := sortedLambda_pos hn hpd 0
  have hab := (sortedLambda_strictMono H.toLinearMap hn).monotone (Fin.zero_le (Fin.last (n+1)))
  have hc : 0 ≤ BB.endpointRate (sortedLambda H.toLinearMap hn 0)
      (sortedLambda H.toLinearMap hn (Fin.last (n+1))) := by
    unfold BB.endpointRate
    exact div_nonneg (sub_nonneg.mpr hab) (add_nonneg (ha.trans_le hab).le ha.le)
  have hstates : ∀ j, z j ∈ BB.Local.pairCone M := by
    intro j
    induction j with
    | zero => exact hz
    | succ j ih =>
      rw [hrec j]
      exact frozen_interval_cone H hH ha hab (sorted_spectral_bounds H.toLinearMap hn) hM (η j) ih
  exact v.trajectory_bound hc z η hstates hrec k

end BB.Operator
