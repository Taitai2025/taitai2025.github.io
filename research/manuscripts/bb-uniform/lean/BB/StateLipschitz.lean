import BB.ScalarStep

set_option autoImplicit false

namespace BB.Spectral
variable {ι : Type*} [Fintype ι]

noncomputable def quotientLip (ι : Type*) [Fintype ι] (a b χ : ℝ) : ℝ :=
  2 * (Fintype.card ι : ℝ) * χ * (1+b/a) / a

noncomputable def stateLip (ι : Type*) [Fintype ι] (a b χ M : ℝ) : ℝ :=
  b/a + b*M*quotientLip ι a b χ

/-- The difference estimate when the first state has the larger preceding gradient. -/
theorem stateMap_lipschitz_ordered {lam w : ι → ℝ} {a b χ M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM : 0 ≤ M)
    (hw1 : ∀ i, 1 ≤ w i) (hwχ : ∀ i, w i ≤ χ)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    {z z' : State ι} (hz : Cone M z)
    (hu : z.1 ≠ 0) (hu' : z'.1 ≠ 0) (horder : ‖z'.1‖ ≤ ‖z.1‖) :
    ‖stateMap lam w z - stateMap lam w z'‖ ≤ stateLip ι a b χ M * ‖z-z'‖ := by
  let C := quotientLip ι a b χ
  let d := b/a-1
  let E := |vectorAlpha lam w z.1 - vectorAlpha lam w z'.1|
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hk : 1 ≤ b/a := (one_le_div ha).mpr hab
  have hd : 0 ≤ d := by dsimp [d]; linarith only [hk]
  have hC : 0 ≤ C := by dsimp [C,quotientLip]; positivity
  have hE : 0 ≤ E := abs_nonneg _
  have hbM : 0 ≤ b*M := mul_nonneg (le_of_lt hb) hM
  have hK : 1 ≤ stateLip ι a b χ M := by
    unfold stateLip
    have hrest : 0 ≤ b*M*C := mul_nonneg hbM hC
    change 0 ≤ b*M*quotientLip ι a b χ at hrest
    linarith only [hk,hrest]
  have hrel : E*‖z.1‖ ≤ C*‖z.1-z'.1‖ :=
    vectorAlpha_relative_lipschitz_ordered ha hab hχ hw1 hwχ hlama hlamb hu hu' horder
  obtain ⟨hlo,hhi⟩ := vectorAlpha_bounds ha hab hw1 hlama hlamb hu'
  have hcoord : ∀ i, |diagonalStep lam (vectorAlpha lam w z.1) z.2 i -
      diagonalStep lam (vectorAlpha lam w z'.1) z'.2 i| ≤
      stateLip ι a b χ M*‖z-z'‖ := by
    intro i
    have hm : |1-vectorAlpha lam w z'.1*lam i| ≤ d :=
      multiplier_bound ha hab (hlama i) (hlamb i) hlo hhi
    have hl0 : 0 ≤ lam i := le_trans (le_of_lt ha) (hlama i)
    have hlabs : |lam i| ≤ b := by simpa only [abs_of_nonneg hl0] using hlamb i
    have hvd : |z.2 i-z'.2 i| ≤ ‖z.2-z'.2‖ := by simpa using norm_le_pi_norm (z.2-z'.2) i
    have hv : |z.2 i| ≤ ‖z.2‖ := by simpa using norm_le_pi_norm z.2 i
    have hterm1 : |(1-vectorAlpha lam w z'.1*lam i)*(z.2 i-z'.2 i)| ≤ d*‖z.2-z'.2‖ := by
      rw [abs_mul]
      exact mul_le_mul hm hvd (abs_nonneg _) hd
    have hterm2 : |(vectorAlpha lam w z'.1-vectorAlpha lam w z.1)*lam i*z.2 i| ≤ E*b*‖z.2‖ := by
      rw [abs_mul,abs_mul,abs_sub_comm (vectorAlpha lam w z'.1) (vectorAlpha lam w z.1)]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hlabs hE) hv (abs_nonneg _) (mul_nonneg hE (le_of_lt hb))
    have hterm3 : E*b*‖z.2‖ ≤ b*M*(E*‖z.1‖) := by
      have hh := mul_le_mul_of_nonneg_left hz (mul_nonneg hE (le_of_lt hb))
      unfold Cone at hh
      nlinarith only [hh]
    have hid : diagonalStep lam (vectorAlpha lam w z.1) z.2 i -
        diagonalStep lam (vectorAlpha lam w z'.1) z'.2 i =
        (1-vectorAlpha lam w z'.1*lam i)*(z.2 i-z'.2 i) +
        (vectorAlpha lam w z'.1-vectorAlpha lam w z.1)*lam i*z.2 i := by
      unfold diagonalStep
      ring
    calc
      _ = |(1-vectorAlpha lam w z'.1*lam i)*(z.2 i-z'.2 i) +
          (vectorAlpha lam w z'.1-vectorAlpha lam w z.1)*lam i*z.2 i| := congrArg abs hid
      _ ≤ |(1-vectorAlpha lam w z'.1*lam i)*(z.2 i-z'.2 i)| +
          |(vectorAlpha lam w z'.1-vectorAlpha lam w z.1)*lam i*z.2 i| := abs_add _ _
      _ ≤ d*‖z.2-z'.2‖ + E*b*‖z.2‖ := add_le_add hterm1 hterm2
      _ ≤ d*‖z.2-z'.2‖ + b*M*(E*‖z.1‖) := add_le_add_left hterm3 _
      _ ≤ d*‖z.2-z'.2‖ + b*M*(C*‖z.1-z'.1‖) :=
        add_le_add_left (mul_le_mul_of_nonneg_left hrel hbM) _
      _ ≤ d*‖z-z'‖ + b*M*(C*‖z-z'‖) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (norm_snd_le (z-z')) hd
        · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_fst_le (z-z')) hC) hbM
      _ ≤ stateLip ι a b χ M*‖z-z'‖ := by
        dsimp [d,C,stateLip]
        nlinarith only [norm_nonneg (z-z')]
  apply norm_prod_le_iff.mpr
  constructor
  · change ‖z.2-z'.2‖ ≤ stateLip ι a b χ M*‖z-z'‖
    exact (norm_snd_le (z-z')).trans (by nlinarith only [hK,norm_nonneg (z-z')])
  · apply (pi_norm_le_iff_of_nonneg (mul_nonneg (le_trans (by norm_num) hK) (norm_nonneg _))).mpr
    exact hcoord

/-- One common global Lipschitz bound on the admissible cone. -/
theorem stateMap_lipschitz {lam w : ι → ℝ} {a b χ M : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM : 0 ≤ M)
    (hw1 : ∀ i, 1 ≤ w i) (hwχ : ∀ i, w i ≤ χ)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    {z z' : State ι} (hz : Cone M z) (hz' : Cone M z') :
    ‖stateMap lam w z - stateMap lam w z'‖ ≤ stateLip ι a b χ M * ‖z-z'‖ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hC : 0 ≤ quotientLip ι a b χ := by unfold quotientLip; positivity
  have hK : b/a ≤ stateLip ι a b χ M := by
    unfold stateLip
    have hh := mul_nonneg (mul_nonneg (le_of_lt hb) hM) hC
    linarith only [hh]
  by_cases hu : z.1 = 0
  · have hzero := cone_eq_zero_of_fst hz hu
    subst z
    simp only [stateMap_zero,zero_sub,norm_neg]
    exact (stateMap_norm ha hab hw1 hlama hlamb hz').trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  by_cases hu' : z'.1 = 0
  · have hzero := cone_eq_zero_of_fst hz' hu'
    subst z'
    simp only [stateMap_zero,sub_zero]
    exact (stateMap_norm ha hab hw1 hlama hlamb hz).trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _))
  rcases le_total ‖z.1‖ ‖z'.1‖ with hle | hge
  · have hh := stateMap_lipschitz_ordered ha hab hχ hM hw1 hwχ hlama hlamb hz' hu' hu hle
    simpa only [norm_sub_rev] using hh
  · exact stateMap_lipschitz_ordered ha hab hχ hM hw1 hwχ hlama hlamb hz hu hu' hge

end BB.Spectral
