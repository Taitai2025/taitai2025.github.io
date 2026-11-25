import BB.SpectralLipschitz

set_option autoImplicit false

namespace BB.Spectral
variable {ι : Type*} [Fintype ι]

abbrev State (ι : Type*) := (ι → ℝ) × (ι → ℝ)

def Cone (M : ℝ) (z : State ι) : Prop := ‖z.2‖ ≤ M * ‖z.1‖

noncomputable def diagonalStep (lam : ι → ℝ) (s : ℝ) (v : ι → ℝ) : ι → ℝ :=
  fun i => (1-s*lam i)*v i

noncomputable def stateMap (lam w : ι → ℝ) (z : State ι) : State ι :=
  (z.2, diagonalStep lam (vectorAlpha lam w z.1) z.2)

/-- The scalar spectral multiplier bound used to preserve the state cone. -/
theorem multiplier_bound {a b l s : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hl : a ≤ l) (hlb : l ≤ b) (hs : 1/b ≤ s) (hsa : s ≤ 1/a) :
    |1-s*l| ≤ b/a-1 := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hs0 : 0 ≤ s := le_trans (le_of_lt (one_div_pos.mpr hb)) hs
  have hl0 : 0 ≤ l := le_trans (le_of_lt ha) hl
  have hup : s*l ≤ b/a := by
    have hh := mul_le_mul hsa hlb hl0 (le_of_lt (one_div_pos.mpr ha))
    convert hh using 1 <;> ring
  have hlo : a/b ≤ s*l := by
    have hh := mul_le_mul hs hl (le_of_lt ha) hs0
    convert hh using 1 <;> ring
  have hid : b/a+a/b-2 = (b-a)^2/(a*b) := by
    field_simp
    <;> ring
  have hcmp : 0 ≤ b/a+a/b-2 := by
    rw [hid]
    positivity
  apply abs_le.mpr
  constructor <;> linarith only [hup,hlo,hcmp]

/-- Sup-norm diagonal operator estimate. -/
theorem diagonalStep_bound {lam : ι → ℝ} {s d : ℝ} (hd : 0 ≤ d)
    (hm : ∀ i, |1-s*lam i| ≤ d) (v : ι → ℝ) :
    ‖diagonalStep lam s v‖ ≤ d*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hd (norm_nonneg v))).mpr
  intro i
  change |(1-s*lam i)*v i| ≤ d*‖v‖
  rw [abs_mul]
  exact mul_le_mul (hm i) (by simpa using norm_le_pi_norm v i) (abs_nonneg _) hd

/-- A zero preceding gradient forces the whole admissible state to be zero. -/
theorem cone_eq_zero_of_fst {M : ℝ} {z : State ι} (hz : Cone M z) (hu : z.1 = 0) : z = 0 := by
  have hv : z.2 = 0 := by
    apply norm_eq_zero.mp
    unfold Cone at hz
    rw [hu,norm_zero,mul_zero] at hz
    exact le_antisymm hz (norm_nonneg _)
  exact Prod.ext hu hv

@[simp] theorem stateMap_zero (lam w : ι → ℝ) : stateMap lam w 0 = 0 := by
  ext i <;> simp [stateMap,diagonalStep]

/-- Positive homogeneity is in fact valid for every real scalar. -/
theorem stateMap_smul (lam w : ι → ℝ) (z : State ι) (t : ℝ) :
    stateMap lam w (t • z) = t • stateMap lam w z := by
  by_cases ht : t = 0
  · simp [ht]
  · have hα : vectorAlpha lam w (t • z.1) = vectorAlpha lam w z.1 := vectorAlpha_smul lam w z.1 ht
    apply Prod.ext
    · rfl
    · funext i
      change (1-vectorAlpha lam w (t • z.1)*lam i)*(t*z.2 i) =
        t*((1-vectorAlpha lam w z.1*lam i)*z.2 i)
      rw [hα]
      ring

/-- Every admissible scalar spectral map preserves the cone. -/
theorem stateMap_cone {lam w : ι → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (hM : b/a-1 ≤ M) {z : State ι} (hz : Cone M z) :
    Cone M (stateMap lam w z) := by
  by_cases hu : z.1 = 0
  · have hzero := cone_eq_zero_of_fst hz hu
    subst z
    simp [Cone]
  · obtain ⟨hlo,hhi⟩ := vectorAlpha_bounds ha hab hw hlama hlamb hu
    have hd : 0 ≤ b/a-1 := by
      have := (one_le_div ha).mpr hab
      linarith
    have hbound := diagonalStep_bound hd (fun i => multiplier_bound ha hab (hlama i) (hlamb i) hlo hhi) z.2
    unfold Cone stateMap
    exact hbound.trans (mul_le_mul_of_nonneg_right hM (norm_nonneg z.2))

/-- Uniform one-step growth in the sup norm; the constant is conservative. -/
theorem stateMap_norm {lam w : ι → ℝ} {a b M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    {z : State ι} (hz : Cone M z) : ‖stateMap lam w z‖ ≤ (b/a)*‖z‖ := by
  by_cases hu : z.1 = 0
  · have hzero := cone_eq_zero_of_fst hz hu
    subst z
    simp
  · obtain ⟨hlo,hhi⟩ := vectorAlpha_bounds ha hab hw hlama hlamb hu
    have hk : 1 ≤ b/a := (one_le_div ha).mpr hab
    have hd : 0 ≤ b/a-1 := by linarith
    have hbound := diagonalStep_bound hd (fun i => multiplier_bound ha hab (hlama i) (hlamb i) hlo hhi) z.2
    apply norm_prod_le_iff.mpr
    constructor
    · change ‖z.2‖ ≤ (b/a)*‖z‖
      exact (norm_snd_le z).trans (by nlinarith only [hk,norm_nonneg z])
    · change ‖diagonalStep lam (vectorAlpha lam w z.1) z.2‖ ≤ (b/a)*‖z‖
      calc
        _ ≤ (b/a-1)*‖z.2‖ := hbound
        _ ≤ (b/a-1)*‖z‖ := mul_le_mul_of_nonneg_left (norm_snd_le z) hd
        _ ≤ (b/a)*‖z‖ := by nlinarith only [norm_nonneg z]

end BB.Spectral
