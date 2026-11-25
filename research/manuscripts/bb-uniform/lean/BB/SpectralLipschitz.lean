import BB.Spectral
import Mathlib.Analysis.NormedSpace.Basic

set_option autoImplicit false

namespace BB.Spectral
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

noncomputable def quadraticForm (w u : ι → ℝ) : ℝ := ∑ i, w i * (u i)^2
noncomputable def vectorAlpha (lam w u : ι → ℝ) : ℝ :=
  quadraticForm w u / quadraticForm (fun i => w i * lam i) u

/-- The sum of squared coordinates dominates the squared sup norm. -/
theorem sum_sq_ge_norm_sq (u : ι → ℝ) : ‖u‖^2 ≤ ∑ i, (u i)^2 := by
  have hs : 0 ≤ ∑ i, (u i)^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hnorm : ‖u‖ ≤ Real.sqrt (∑ i, (u i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply (Real.le_sqrt (abs_nonneg _) hs).mpr
    rw [sq_abs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (u j)) (Finset.mem_univ i)
  have hsq := Real.sq_sqrt hs
  nlinarith [norm_nonneg u, Real.sqrt_nonneg (∑ i, (u i)^2)]

/-- Uniform ellipticity of a diagonal quadratic form, in the sup norm. -/
theorem quadraticForm_lower {w : ι → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hw : ∀ i, m ≤ w i) (u : ι → ℝ) : m * ‖u‖^2 ≤ quadraticForm w u := by
  calc
    m * ‖u‖^2 ≤ m * ∑ i, (u i)^2 := mul_le_mul_of_nonneg_left (sum_sq_ge_norm_sq u) hm
    _ ≤ quadraticForm w u := by
      unfold quadraticForm
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (sq_nonneg _))

/-- Difference estimate for a diagonal quadratic form. -/
theorem quadraticForm_diff {w : ι → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hw : ∀ i, |w i| ≤ C) (u v : ι → ℝ) :
    |quadraticForm w u - quadraticForm w v| ≤
      (Fintype.card ι : ℝ) * C * (‖u‖ + ‖v‖) * ‖u-v‖ := by
  have hterm : ∀ i, |w i*(u i)^2 - w i*(v i)^2| ≤
      C * ‖u-v‖ * (‖u‖ + ‖v‖) := by
    intro i
    have hd : |u i - v i| ≤ ‖u-v‖ := by simpa using norm_le_pi_norm (u-v) i
    have hs : |u i + v i| ≤ ‖u‖ + ‖v‖ := by
      calc
        |u i + v i| ≤ |u i| + |v i| := abs_add _ _
        _ ≤ ‖u‖ + ‖v‖ := add_le_add (by simpa using norm_le_pi_norm u i)
          (by simpa using norm_le_pi_norm v i)
    have hid : w i*(u i)^2 - w i*(v i)^2 = w i*(u i-v i)*(u i+v i) := by ring
    rw [hid,abs_mul,abs_mul]
    exact mul_le_mul (mul_le_mul (hw i) hd (abs_nonneg _) hC) hs (abs_nonneg _) (by positivity)
  unfold quadraticForm
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, (w i * (u i)^2 - w i * (v i)^2)| ≤
        ∑ i, |w i * (u i)^2 - w i * (v i)^2| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, C * ‖u-v‖ * (‖u‖+‖v‖) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = (Fintype.card ι : ℝ) * C * (‖u‖+‖v‖) * ‖u-v‖ := by simp; ring

/-- The vector quotient agrees with the preceding energy-based definition. -/
theorem vectorAlpha_eq (lam w u : ι → ℝ) :
    vectorAlpha lam w u = alpha lam w (fun i => (u i)^2) := by
  unfold vectorAlpha quadraticForm alpha numerator denominator
  congr 1

/-- A nonzero vector gives a positive denominator under a positive spectrum. -/
theorem vector_denominator_pos {lam w u : ι → ℝ} {a : ℝ}
    (ha : 0 < a) (hw : ∀ i, 1 ≤ w i) (hlam : ∀ i, a ≤ lam i)
    (hu : u ≠ 0) : 0 < quadraticForm (fun i => w i * lam i) u := by
  have hcoef : ∀ i, a ≤ w i * lam i := by
    intro i
    have hl : 0 ≤ lam i := le_trans (le_of_lt ha) (hlam i)
    nlinarith only [hlam i, mul_le_mul_of_nonneg_right (hw i) hl]
  have hlow := quadraticForm_lower (le_of_lt ha) hcoef u
  exact lt_of_lt_of_le (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hu))) hlow

/-- Positivity and upper/lower bounds for the vector quotient. -/
theorem vectorAlpha_bounds {lam w u : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hu : u ≠ 0) :
    1/b ≤ vectorAlpha lam w u ∧ vectorAlpha lam w u ≤ 1/a := by
  rw [vectorAlpha_eq]
  have hnum : 0 < numerator w (fun i => (u i)^2) := by
    have hh := quadraticForm_lower (show (0:ℝ) ≤ 1 by norm_num) hw u
    have hnorm : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    change 0 < quadraticForm w u
    linarith
  exact alpha_bounds ha hab (fun i => sq_nonneg _) (fun i => le_trans (by norm_num) (hw i)) hlama hlamb hnum

/-- Homogeneity of degree zero of the spectral quotient, including at zero. -/
theorem vectorAlpha_smul (lam w u : ι → ℝ) {t : ℝ} (ht : t ≠ 0) :
    vectorAlpha lam w (t • u) = vectorAlpha lam w u := by
  have hQ (q : ι → ℝ) : quadraticForm q (t • u) = t^2 * quadraticForm q u := by
    unfold quadraticForm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  unfold vectorAlpha
  rw [hQ, hQ]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

/-- A direct relative Lipschitz bound. The first vector has the larger norm.
This constant is deliberately conservative and independent of multiplicities. -/
theorem vectorAlpha_relative_lipschitz_ordered
    {lam w u v : ι → ℝ} {a b χ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ)
    (hw1 : ∀ i, 1 ≤ w i) (hwχ : ∀ i, w i ≤ χ)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (hu : u ≠ 0) (hv : v ≠ 0) (horder : ‖v‖ ≤ ‖u‖) :
    |vectorAlpha lam w u - vectorAlpha lam w v| * ‖u‖ ≤
      (2 * (Fintype.card ι : ℝ) * χ * (1+b/a) / a) * ‖u-v‖ := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hr : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have ha0 : a ≠ 0 := ne_of_gt ha
  have hDu := vector_denominator_pos ha hw1 hlama hu
  have hDv := vector_denominator_pos ha hw1 hlama hv
  have haw : ∀ i, |w i| ≤ χ := by
    intro i
    rw [abs_of_nonneg (le_trans (by norm_num) (hw1 i))]
    exact hwχ i
  have hawl : ∀ i, |w i * lam i| ≤ χ*b := by
    intro i
    have hw0 : 0 ≤ w i := le_trans (by norm_num) (hw1 i)
    have hl0 : 0 ≤ lam i := le_trans (le_of_lt ha) (hlama i)
    rw [abs_of_nonneg (mul_nonneg hw0 hl0)]
    exact mul_le_mul (hwχ i) (hlamb i) hl0 hχ
  have hN := quadraticForm_diff hχ haw u v
  have hD := quadraticForm_diff (mul_nonneg hχ (le_of_lt hb)) hawl v u
  rw [norm_sub_rev, add_comm ‖v‖ ‖u‖] at hD
  obtain ⟨hαlo,hαhi⟩ := vectorAlpha_bounds ha hab hw1 hlama hlamb hv
  have hα0 : 0 ≤ vectorAlpha lam w v := le_trans (le_of_lt (one_div_pos.mpr hb)) hαlo
  have hαabs : |vectorAlpha lam w v| ≤ 1/a := by rwa [abs_of_nonneg hα0]
  have hid : (vectorAlpha lam w u - vectorAlpha lam w v) * quadraticForm (fun i => w i * lam i) u =
      (quadraticForm w u - quadraticForm w v) + vectorAlpha lam w v *
      (quadraticForm (fun i => w i * lam i) v - quadraticForm (fun i => w i * lam i) u) := by
    unfold vectorAlpha
    field_simp [ne_of_gt hDu, ne_of_gt hDv]
    <;> ring
  have hmain : |vectorAlpha lam w u - vectorAlpha lam w v| *
      quadraticForm (fun i => w i * lam i) u ≤
      (Fintype.card ι : ℝ)*χ*(‖u‖+‖v‖)*‖u-v‖ +
      (1/a)*((Fintype.card ι : ℝ)*(χ*b)*(‖u‖+‖v‖)*‖u-v‖) := by
    calc
      _ = |(vectorAlpha lam w u - vectorAlpha lam w v) *
          quadraticForm (fun i => w i * lam i) u| := by rw [abs_mul,abs_of_pos hDu]
      _ = |(quadraticForm w u - quadraticForm w v) + vectorAlpha lam w v *
          (quadraticForm (fun i => w i * lam i) v - quadraticForm (fun i => w i * lam i) u)| := congrArg abs hid
      _ ≤ |quadraticForm w u - quadraticForm w v| + |vectorAlpha lam w v| *
          |quadraticForm (fun i => w i * lam i) v - quadraticForm (fun i => w i * lam i) u| := by
        simpa only [abs_mul] using abs_add (quadraticForm w u - quadraticForm w v)
          (vectorAlpha lam w v * (quadraticForm (fun i => w i * lam i) v - quadraticForm (fun i => w i * lam i) u))
      _ ≤ _ := add_le_add hN (mul_le_mul hαabs hD (abs_nonneg _) (by positivity))
  have hcoef : ∀ i, a ≤ w i * lam i := by
    intro i
    have hl : 0 ≤ lam i := le_trans (le_of_lt ha) (hlama i)
    nlinarith only [hlama i, mul_le_mul_of_nonneg_right (hw1 i) hl]
  have hlow := quadraticForm_lower (le_of_lt ha) hcoef u
  have hscale : 0 ≤ (Fintype.card ι : ℝ)*χ*(1+b/a)*‖u-v‖ := by positivity
  have htwo : ‖u‖+‖v‖ ≤ 2*‖u‖ := by linarith
  have hprod : (|vectorAlpha lam w u - vectorAlpha lam w v| * ‖u‖) * (a*‖u‖) ≤
      ((2*(Fintype.card ι : ℝ)*χ*(1+b/a)/a)*‖u-v‖) * (a*‖u‖) := by
    calc
      _ = |vectorAlpha lam w u - vectorAlpha lam w v| * (a*‖u‖^2) := by ring
      _ ≤ |vectorAlpha lam w u - vectorAlpha lam w v| *
          quadraticForm (fun i => w i * lam i) u := mul_le_mul_of_nonneg_left hlow (abs_nonneg _)
      _ ≤ _ := hmain
      _ = ((Fintype.card ι : ℝ)*χ*(1+b/a)*‖u-v‖)*(‖u‖+‖v‖) := by ring
      _ ≤ ((Fintype.card ι : ℝ)*χ*(1+b/a)*‖u-v‖)*(2*‖u‖) := mul_le_mul_of_nonneg_left htwo hscale
      _ = _ := by field_simp; ring
  exact (mul_le_mul_right (mul_pos ha hr)).mp hprod

/-- Symmetric relative Lipschitz estimate, with the maximum of the two norms. -/
theorem vectorAlpha_relative_lipschitz {lam w u v : ι → ℝ} {a b χ : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ)
    (hw1 : ∀ i, 1 ≤ w i) (hwχ : ∀ i, w i ≤ χ)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hu : u ≠ 0) (hv : v ≠ 0) :
    |vectorAlpha lam w u - vectorAlpha lam w v| * max ‖u‖ ‖v‖ ≤
      (2 * (Fintype.card ι : ℝ) * χ * (1+b/a) / a) * ‖u-v‖ := by
  rcases le_total ‖u‖ ‖v‖ with huv | hvu
  · rw [max_eq_right huv]
    have h := vectorAlpha_relative_lipschitz_ordered ha hab hχ hw1 hwχ hlama hlamb hv hu huv
    simpa only [abs_sub_comm, norm_sub_rev] using h
  · rw [max_eq_left hvu]
    exact vectorAlpha_relative_lipschitz_ordered ha hab hχ hw1 hwχ hlama hlamb hu hv hvu

@[simp] theorem vectorAlpha_zero (lam w : ι → ℝ) : vectorAlpha lam w 0 = 0 := by
  simp [vectorAlpha,quadraticForm]

/-- Support-sensitive quotient bounds for the fixed-ambient-space induction. -/
theorem vectorAlpha_bounds_on_support {lam w u : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hsupport : ∀ i, u i = 0 ∨ (a ≤ lam i ∧ lam i ≤ b)) (hu : u ≠ 0) :
    1/b ≤ vectorAlpha lam w u ∧ vectorAlpha lam w u ≤ 1/a := by
  rw [vectorAlpha_eq]
  have hnum : 0 < numerator w (fun i => (u i)^2) := by
    have hh := quadraticForm_lower (show (0:ℝ) ≤ 1 by norm_num) hw u
    have hnorm : 0 < ‖u‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hu)
    change 0 < quadraticForm w u
    linarith only [hh,hnorm]
  apply alpha_bounds_on_support ha hab (fun i => sq_nonneg _) (fun i => le_trans (by norm_num) (hw i)) _ hnum
  intro i
  rcases hsupport i with hz | hh
  · left; simp [hz]
  · exact Or.inr hh

end BB.Spectral
