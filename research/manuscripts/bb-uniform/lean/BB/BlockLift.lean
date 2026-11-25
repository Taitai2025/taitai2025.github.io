import BB.SignInvariant
import BB.Certificate

set_option autoImplicit false

/-!
# Lifting a diagonal certificate to normed spectral blocks

The block dimensions are unrestricted.  The hypotheses are bounds on the
actual per-block energies, not convergence or Lyapunov assumptions about
the block iteration.  A scalar certificate is subsequently supplied by the
finite-spectrum induction.
-/

namespace BB.Blocks

open BB.Spectral BB.Gluing
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

abbrev BState (E : ι → Type*) := (∀ i, E i) × (∀ i, E i)

noncomputable def radius (u : ∀ i, E i) : ι → ℝ := fun i => ‖u i‖
noncomputable def stateRadius (z : BState E) : State ι := (radius z.1,radius z.2)

def blockCone (M : ℝ) (z : BState E) : Prop := ‖z.2‖ ≤ M*‖z.1‖

@[simp] theorem radius_norm (u : ∀ i, E i) : ‖radius u‖ = ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa [radius] using norm_le_pi_norm u i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa [radius] using norm_le_pi_norm (radius u) i

@[simp] theorem stateRadius_norm (z : BState E) : ‖stateRadius z‖ = ‖z‖ := by
  simp only [stateRadius,Prod.norm_def,radius_norm]

@[simp] theorem stateRadius_cone (M : ℝ) (z : BState E) :
    Cone M (stateRadius z) ↔ blockCone M z := by
  simp only [Cone,stateRadius,radius_norm,blockCone]

@[simp] theorem abs_radius (u : ∀ i, E i) : absVector (radius u) = radius u := by
  funext i
  exact abs_of_nonneg (norm_nonneg _)

@[simp] theorem abs_stateRadius (z : BState E) : absState (stateRadius z) = stateRadius z := by
  simp [absState,stateRadius]

theorem radius_nonexpansive (u v : ∀ i, E i) : ‖radius u-radius v‖ ≤ ‖u-v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change |‖u i‖-‖v i‖| ≤ ‖u-v‖
  exact (abs_norm_sub_norm_le _ _).trans (norm_le_pi_norm (u-v) i)

theorem stateRadius_nonexpansive (z z' : BState E) :
    ‖stateRadius z-stateRadius z'‖ ≤ ‖z-z'‖ := by
  apply norm_prod_le_iff.mpr
  exact ⟨(radius_nonexpansive _ _).trans (norm_fst_le (z-z')),
    (radius_nonexpansive _ _).trans (norm_snd_le (z-z'))⟩

theorem radius_smul (u : ∀ i, E i) {t : ℝ} (ht : 0 ≤ t) :
    radius (t • u) = t • radius u := by
  funext i
  change ‖t • u i‖ = t * ‖u i‖
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]

theorem stateRadius_smul (z : BState E) {t : ℝ} (ht : 0 ≤ t) :
    stateRadius (t • z) = t • stateRadius z :=
  Prod.ext (radius_smul _ ht) (radius_smul _ ht)

noncomputable def effectiveWeight (q : ∀ i, E i → ℝ) (u : ∀ i, E i) (i : ι) : ℝ :=
  by classical exact if u i = 0 then 1 else q i (u i) / ‖u i‖^2

/-- Normalize each nonzero block energy; zero blocks use weight one. -/
theorem effectiveWeight_bounds {q : ∀ i, E i → ℝ} {χ : ℝ} (hχ : 1 ≤ χ)
    (hqlo : ∀ i x, ‖x‖^2 ≤ q i x) (hqhi : ∀ i x, q i x ≤ χ*‖x‖^2)
    (u : ∀ i, E i) (i : ι) : 1 ≤ effectiveWeight q u i ∧ effectiveWeight q u i ≤ χ := by
  unfold effectiveWeight
  split_ifs with hz
  · exact ⟨le_refl _,hχ⟩
  · have hn : 0 < ‖u i‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
    constructor
    · exact (one_le_div hn).mpr (hqlo i (u i))
    · exact (div_le_iff hn).mpr (hqhi i (u i))

/-- No energy is lost in the zero-block convention. -/
theorem effectiveWeight_energy {q : ∀ i, E i → ℝ} {χ : ℝ}
    (hqlo : ∀ i x, ‖x‖^2 ≤ q i x) (hqhi : ∀ i x, q i x ≤ χ*‖x‖^2)
    (u : ∀ i, E i) (i : ι) : effectiveWeight q u i * ‖u i‖^2 = q i (u i) := by
  unfold effectiveWeight
  split_ifs with hz
  · have hlo := hqlo i (u i)
    have hhi := hqhi i (u i)
    simp only [hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),mul_zero] at *
    linarith
  · exact div_mul_cancel₀ _ (ne_of_gt (sq_pos_of_pos (norm_pos_iff.mpr hz)))

noncomputable def blockAlpha (lam : ι → ℝ) (q : ∀ i, E i → ℝ) (u : ∀ i, E i) : ℝ :=
  (∑ i, q i (u i)) / (∑ i, lam i * q i (u i))

/-- Exact equality of the block quotient and its effective scalar quotient. -/
theorem blockAlpha_eq {q : ∀ i, E i → ℝ} {χ : ℝ}
    (hqlo : ∀ i x, ‖x‖^2 ≤ q i x) (hqhi : ∀ i x, q i x ≤ χ*‖x‖^2)
    (lam : ι → ℝ) (u : ∀ i, E i) :
    blockAlpha lam q u = vectorAlpha lam (effectiveWeight q u) (radius u) := by
  unfold blockAlpha vectorAlpha quadraticForm radius
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    exact (effectiveWeight_energy hqlo hqhi u i).symm
  · apply Finset.sum_congr rfl
    intro i _
    rw [show effectiveWeight q u i * lam i * ‖u i‖^2 =
      lam i*(effectiveWeight q u i*‖u i‖^2) by ring]
    rw [effectiveWeight_energy hqlo hqhi]

noncomputable def blockMap (lam : ι → ℝ) (q : ∀ i, E i → ℝ) (z : BState E) : BState E :=
  (z.2, fun i => (1-blockAlpha lam q z.1*lam i) • z.2 i)

/-- The block update and diagonal update have exactly the same component magnitudes. -/
theorem stateRadius_blockMap {q : ∀ i, E i → ℝ} {χ : ℝ}
    (hqlo : ∀ i x, ‖x‖^2 ≤ q i x) (hqhi : ∀ i x, q i x ≤ χ*‖x‖^2)
    (lam : ι → ℝ) (z : BState E) :
    stateRadius (blockMap lam q z) =
      absState (stateMap lam (effectiveWeight q z.1) (stateRadius z)) := by
  apply Prod.ext
  · exact (abs_radius z.2).symm
  · funext i
    change ‖(1-blockAlpha lam q z.1*lam i) • z.2 i‖ =
      |(1-vectorAlpha lam (effectiveWeight q z.1) (radius z.1)*lam i)*‖z.2 i‖|
    rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (norm_nonneg _),blockAlpha_eq hqlo hqhi]

abbrev ScalarWeights (ι : Type*) (χ : ℝ) := {w : ι → ℝ // ∀ i, 1 ≤ w i ∧ w i ≤ χ}

/-- Transfer a common scalar certificate to arbitrary normed spectral blocks. -/
noncomputable def liftCertificate {Ω : Type*} {lam : ι → ℝ} {χ M c : ℝ}
    (q : Ω → ∀ i, E i → ℝ) (hχ : 1 ≤ χ)
    (hqlo : ∀ ω i x, ‖x‖^2 ≤ q ω i x)
    (hqhi : ∀ ω i x, q ω i x ≤ χ*‖x‖^2)
    (v : Certificate (fun w : ScalarWeights ι χ => stateMap lam w.val) {z | Cone M z} c)
    (habs : ∀ z, v.value (absState z) = v.value z) :
    Certificate (fun ω => blockMap lam (q ω)) {z | blockCone M z} c where
  value := fun z => v.value (stateRadius z)
  prefactor := v.prefactor
  lipConstant := v.lipConstant
  prefactor_ge_one := v.prefactor_ge_one
  lipConstant_nonneg := v.lipConstant_nonneg
  lower := by
    intro z hz
    have h := v.lower (stateRadius z) ((stateRadius_cone M z).mpr hz)
    simpa only [stateRadius_norm] using h
  upper := by
    intro z hz
    have h := v.upper (stateRadius z) ((stateRadius_cone M z).mpr hz)
    simpa only [stateRadius_norm] using h
  lipschitz := by
    intro z z' hz hz'
    exact (v.lipschitz (stateRadius z) (stateRadius z')
      ((stateRadius_cone M z).mpr hz) ((stateRadius_cone M z').mpr hz')).trans
      (mul_le_mul_of_nonneg_left (stateRadius_nonexpansive z z') v.lipConstant_nonneg)
  homogeneous := by
    intro z hz t ht
    change v.value (stateRadius (t • z)) = t * v.value (stateRadius z)
    rw [stateRadius_smul z ht]
    exact v.homogeneous (stateRadius z) ((stateRadius_cone M z).mpr hz) t ht
  decrease := by
    intro ω z hz
    let w : ScalarWeights ι χ := ⟨effectiveWeight (q ω) z.1,
      effectiveWeight_bounds hχ (hqlo ω) (hqhi ω) z.1⟩
    change v.value (stateRadius (blockMap lam (q ω) z)) ≤ c * v.value (stateRadius z)
    rw [stateRadius_blockMap (hqlo ω) (hqhi ω),habs]
    exact v.decrease w (stateRadius z) ((stateRadius_cone M z).mpr hz)

end BB.Blocks
