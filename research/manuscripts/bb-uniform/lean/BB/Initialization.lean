import BB.MainTheorem
import BB.OperatorLipschitz
import BB.NormConsequences

/-! # Matched and arbitrary first-step estimates in the original norm -/

set_option autoImplicit false
noncomputable section
namespace BB.Operator

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_fst_le_pairNorm (z : E × E) : ‖z.1‖ ≤ pairNorm z :=
  (le_max_left _ _).trans (norm_le_pairNorm z)

theorem norm_snd_le_pairNorm (z : E × E) : ‖z.2‖ ≤ pairNorm z :=
  (le_max_right _ _).trans (norm_le_pairNorm z)

theorem matched_pairNorm (g : E) : pairNorm (g,g) = Real.sqrt 2*‖g‖ := by
  unfold pairNorm
  change Real.sqrt (‖g‖^2+‖g‖^2) = _
  rw [show ‖g‖^2+‖g‖^2 = 2*‖g‖^2 by ring,
    Real.sqrt_mul (by norm_num),Real.sqrt_sq (norm_nonneg g)]

/-- The exact manuscript constant for one state update. -/
def oneStepPairBound (a b : ℝ) : ℝ := Real.sqrt (1+(b/a-1)^2)

theorem oneStepPairBound_nonneg (a b : ℝ) : 0 ≤ oneStepPairBound a b := Real.sqrt_nonneg _

theorem oneStepPairBound_ge_one (a b : ℝ) : 1 ≤ oneStepPairBound a b := by
  apply (Real.le_sqrt (by norm_num) (by positivity)).mpr
  nlinarith [sq_nonneg (b/a-1)]

theorem pairNorm_of_component_bound {a b : ℝ} {v v' : E}
    (hd : 0 ≤ b/a-1) (h : ‖v'‖ ≤ (b/a-1)*‖v‖) :
    pairNorm (v,v') ≤ oneStepPairBound a b*‖v‖ := by
  have hp : 0 ≤ (b/a-1)*‖v‖ := mul_nonneg hd (norm_nonneg v)
  have hs : ‖v'‖^2 ≤ (b/a-1)^2*‖v‖^2 := by nlinarith [norm_nonneg v']
  unfold pairNorm oneStepPairBound
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · have he := Real.sq_sqrt (show 0 ≤ 1+(b/a-1)^2 by positivity)
    change ‖v‖^2+‖v'‖^2 ≤ _
    nlinarith only [hs,he]

/-- Iteration of a Euclidean certificate, without changing its prefactor. -/
theorem EuclideanCertificate.trajectory_bound {Ω : Type*} {T : Ω → E × E → E × E}
    {M c K : ℝ} (v : EuclideanCertificate T M c K) (hc : 0 ≤ c)
    (w : ℕ → Ω) (z : ℕ → E × E) (hz : ∀ k, stateCone M (z k))
    (hrec : ∀ k, z (k+1) = T (w k) (z k)) (k : ℕ) :
    pairNorm (z k) ≤ K*c^k*pairNorm (z 0) := by
  have hv : ∀ j, v.value (z j) ≤ c^j*v.value (z 0) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [hrec j]
      have h := mul_le_mul_of_nonneg_left ih hc
      calc
        v.value (T (w j) (z j)) ≤ c*v.value (z j) := v.decrease (w j) (z j) (hz j)
        _ ≤ c*(c^j*v.value (z 0)) := h
        _ = c^(j+1)*v.value (z 0) := by rw [pow_succ]; ring
  have h := mul_le_mul_of_nonneg_left (v.upper (z 0) (hz 0)) (pow_nonneg hc k)
  exact (v.lower (z k) (hz k)).trans ((hv k).trans (by nlinarith only [h]))

/-- The square-root-two matched-start constant follows from the same common certificate. -/
theorem matched_gradient_bound {Ω : Type*} {T : Ω → E × E → E × E} {M c K : ℝ}
    (v : EuclideanCertificate T M c K) (hc : 0 ≤ c) (hM : 1 ≤ M)
    (hT : ∀ w z, stateCone M z → stateCone M (T w z))
    (w : ℕ → Ω) (g : ℕ → E)
    (hrec : ∀ k, (g k,g (k+1)) = T (w k) (g (k-1),g k)) (k : ℕ) :
    ‖g k‖ ≤ Real.sqrt 2*K*c^k*‖g 0‖ := by
  let z : ℕ → E × E := fun j => (g (j-1),g j)
  have hz0 : stateCone M (z 0) := by
    change ‖g 0‖ ≤ M*‖g 0‖
    exact le_mul_of_one_le_left (norm_nonneg _) hM
  have hr : ∀ j, z (j+1) = T (w j) (z j) := by
    intro j
    simpa only [z,Nat.add_sub_cancel] using hrec j
  have hz : ∀ j, stateCone M (z j) := by
    intro j
    induction j with
    | zero => exact hz0
    | succ j ih => rw [hr j]; exact hT (w j) (z j) ih
  have hb := v.trajectory_bound hc w z hz hr k
  have hm : pairNorm (z 0) = Real.sqrt 2*‖g 0‖ := matched_pairNorm (g 0)
  rw [hm] at hb
  exact (norm_snd_le_pairNorm (z k)).trans (by nlinarith only [hb])

variable [FiniteDimensional ℝ E]

/-- The original Euclidean cone is forward invariant under every admissible operator weight. -/
theorem stateMap_cone {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hM : b/a-1 ≤ M) {z : E × E} (hz : stateCone M z) :
    stateCone M (stateMap H W z) := by
  by_cases hu : z.1 = 0
  · have hv : z.2 = 0 := by
      unfold stateCone at hz
      rw [hu,norm_zero,mul_zero] at hz
      exact norm_eq_zero.mp (le_antisymm hz (norm_nonneg _))
    simp [stateCone,stateMap,hv]
  · have hs := weightedAlpha_bounds hH hcomm hWpd ha hab hspec hu
    exact (spectral_step_norm_bound hH ha hab hspec hs.1 hs.2 z.2).trans
      (mul_le_mul_of_nonneg_right hM (norm_nonneg z.2))

/-- An arbitrary first step is absorbed in g₁; no upper or lower bound on that
first scalar is needed for the subsequent estimate relative to g₁. -/
theorem arbitrary_first_gradient_bound {Ω : Type*} {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (W : Ω → E →ₗ[ℝ] E)
    (hcomm : ∀ ω, Function.Commute H (W ω))
    (hWpd : ∀ ω x, x ≠ 0 → 0 < @inner ℝ _ _ x (W ω x))
    {a b M c K : ℝ} (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hM : b/a-1 ≤ M) (v : EuclideanCertificate (fun ω => stateMap H (W ω)) M c K)
    (w : ℕ → Ω) (g : ℕ → E) (α₀ : ℝ)
    (hfirst : g 1 = g 0-α₀ • H (g 0))
    (hrec : ∀ k, g (k+2) = g (k+1)-weightedAlpha H (W (w k)) (g k) • H (g (k+1)))
    (k : ℕ) (hk : 1 ≤ k) :
    ‖g k‖ ≤ max 1 (K*oneStepPairBound a b/c)*c^(k-1)*‖g 1‖ := by
  have hd : 0 ≤ b/a-1 := by have := (one_le_div ha).mpr hab; linarith
  have hg2 : ‖g 2‖ ≤ (b/a-1)*‖g 1‖ := by
    by_cases h0 : g 0 = 0
    · have h1 : g 1 = 0 := by simpa [h0] using hfirst
      have h2 : g 2 = 0 := by simpa [h1] using hrec 0
      simp [h1,h2]
    · have hs := weightedAlpha_bounds hH (hcomm (w 0)) (hWpd (w 0)) ha hab hspec h0
      simpa only [Nat.zero_add] using
        (hrec 0).symm ▸ (spectral_step_norm_bound hH ha hab hspec hs.1 hs.2 (g 1))
  let z : ℕ → E × E := fun j => (g (j+1),g (j+2))
  have hz0 : stateCone M (z 0) :=
    hg2.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
  have hr : ∀ j, z (j+1) = stateMap H (W (w (j+1))) (z j) := by
    intro j
    apply Prod.ext
    · simp [z,stateMap,Nat.add_assoc]
    · simpa [z,stateMap,Nat.add_assoc] using hrec (j+1)
  have hz : ∀ j, stateCone M (z j) := by
    intro j
    induction j with
    | zero => exact hz0
    | succ j ih =>
      rw [hr j]
      exact stateMap_cone hH (hcomm (w (j+1))) (hWpd (w (j+1))) ha hab hspec hM ih
  by_cases hk1 : k = 1
  · subst k
    simpa using le_mul_of_one_le_left (norm_nonneg (g 1)) (le_max_left 1 (K*oneStepPairBound a b/c))
  · have hk2 : 2 ≤ k := by omega
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk2
    have hj : 2+j = j+2 := Nat.add_comm _ _
    rw [hj]
    have hb := v.trajectory_bound hc.le (fun j => w (j+1)) z hz hr j
    have hinit := pairNorm_of_component_bound hd hg2
    have hK : 0 ≤ K := (by norm_num : (0:ℝ) ≤ 1).trans v.prefactor_ge_one
    have hscale := mul_le_mul_of_nonneg_left hinit (mul_nonneg hK (pow_nonneg hc.le j))
    have hfinal : ‖g (j+2)‖ ≤ K*oneStepPairBound a b*c^j*‖g 1‖ := by
      have hh := (norm_snd_le_pairNorm (z j)).trans hb
      change ‖g (j+2)‖ ≤ _ at hh
      change _ ≤ K*c^j*(oneStepPairBound a b*‖g 1‖) at hscale
      nlinarith only [hh,hscale]
    have hcomp : K*oneStepPairBound a b*c^j ≤
        max 1 (K*oneStepPairBound a b/c)*c^(j+1) := by
      have hh := mul_le_mul_of_nonneg_right
        (le_max_right 1 (K*oneStepPairBound a b/c)) (pow_nonneg hc.le (j+1))
      have he : (K*oneStepPairBound a b/c)*c^(j+1) = K*oneStepPairBound a b*c^j := by
        rw [pow_succ]
        field_simp
        <;> ring
      rwa [he] at hh
    have hcomp' := mul_le_mul_of_nonneg_right hcomp (norm_nonneg (g 1))
    have he : j+2-1 = j+1 := by omega
    rw [he]
    exact hfinal.trans hcomp'

end BB.Operator
