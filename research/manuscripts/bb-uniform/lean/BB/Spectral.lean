import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# Spectral quotient algebra and exact examples

The variables `e i` are squared lengths of the mutually orthogonal spectral
components, and `w i` are positive effective weights on these components.
This module proves the finite-sum algebra. It does not assume a convergence
estimate in order to prove any of the quotient or orbit statements.
-/

set_option autoImplicit false

namespace BB.Spectral

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def mass (e : ι → ℝ) : ℝ := ∑ i, e i
noncomputable def firstMoment (lam e : ι → ℝ) : ℝ := ∑ i, lam i * e i
noncomputable def secondMoment (lam e : ι → ℝ) : ℝ := ∑ i, (lam i)^2 * e i
noncomputable def numerator (w e : ι → ℝ) : ℝ := ∑ i, w i * e i
noncomputable def denominator (lam w e : ι → ℝ) : ℝ := ∑ i, w i * lam i * e i
noncomputable def alpha (lam w e : ι → ℝ) : ℝ := numerator w e / denominator lam w e

/-- A positive lower bound on the weights preserves nonzero total energy. -/
theorem numerator_pos {e w : ι → ℝ} {m : ℝ}
    (he : ∀ i, 0 ≤ e i) (hm : 0 < m) (hw : ∀ i, m ≤ w i)
    (hE : 0 < mass e) : 0 < numerator w e := by
  have h : m * mass e ≤ numerator w e := by
    unfold mass numerator
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hw i) (he i))
  exact lt_of_lt_of_le (mul_pos hm hE) h

/-- The weighted denominator lies between the endpoint multiples of its numerator. -/
theorem denominator_bounds {lam w e : ι → ℝ} {a b : ℝ}
    (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 ≤ w i)
    (ha : ∀ i, a ≤ lam i) (hb : ∀ i, lam i ≤ b) :
    a * numerator w e ≤ denominator lam w e ∧
    denominator lam w e ≤ b * numerator w e := by
  constructor
  · unfold numerator denominator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_left (ha i) (mul_nonneg (hw i) (he i))]
  · unfold numerator denominator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith only [mul_le_mul_of_nonneg_left (hb i) (mul_nonneg (hw i) (he i))]

/-- Equation (2.3): every positive spectral quotient is in `[1/b,1/a]`. -/
theorem alpha_bounds {lam w e : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (hnum : 0 < numerator w e) :
    1 / b ≤ alpha lam w e ∧ alpha lam w e ≤ 1 / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨hlo, hhi⟩ := denominator_bounds he hw hlama hlamb
  have hden : 0 < denominator lam w e := lt_of_lt_of_le (mul_pos ha hnum) hlo
  unfold alpha
  constructor
  · apply (div_le_div_iff hb hden).mpr
    nlinarith
  · apply (div_le_div_iff hden ha).mpr
    nlinarith

/-- A variance identity used to justify the ordering of the BB steps. -/
theorem variance_identity (lam e : ι → ℝ) (t : ℝ) :
    (∑ i, e i * (lam i - t)^2) =
      secondMoment lam e - 2*t*firstMoment lam e + t^2*mass e := by
  unfold secondMoment firstMoment mass
  simp_rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Finite weighted Cauchy--Schwarz, proved directly from nonnegative variance. -/
theorem moment_cauchy {lam e : ι → ℝ} (he : ∀ i, 0 ≤ e i)
    (hE : 0 < mass e) : (firstMoment lam e)^2 ≤ mass e * secondMoment lam e := by
  have hv : 0 ≤ ∑ i, e i * (lam i - firstMoment lam e / mass e)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (he i) (sq_nonneg _))
  rw [variance_identity] at hv
  have hE0 : mass e ≠ 0 := ne_of_gt hE
  have hident : secondMoment lam e - 2 * (firstMoment lam e / mass e) * firstMoment lam e +
      (firstMoment lam e / mass e)^2 * mass e =
      (mass e * secondMoment lam e - (firstMoment lam e)^2) / mass e := by
    field_simp
    <;> ring
  rw [hident] at hv
  have hnonneg : 0 ≤ mass e * secondMoment lam e - (firstMoment lam e)^2 :=
    by simpa using (le_div_iff hE).mp hv
  linarith

/-- On a positive spectrum, both BB moment denominators are strictly positive. -/
theorem moments_pos {lam e : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (he : ∀ i, 0 ≤ e i) (hlam : ∀ i, a ≤ lam i) (hE : 0 < mass e) :
    0 < firstMoment lam e ∧ 0 < secondMoment lam e := by
  have hm : a * mass e ≤ firstMoment lam e := by
    unfold mass firstMoment
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hlam i) (he i))
  have h1 : 0 < firstMoment lam e := lt_of_lt_of_le (mul_pos ha hE) hm
  have hm2 : a * firstMoment lam e ≤ secondMoment lam e := by
    unfold firstMoment secondMoment
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have hlam0 : 0 ≤ lam i := le_trans (le_of_lt ha) (hlam i)
    have hh := mul_le_mul_of_nonneg_right (hlam i) (mul_nonneg hlam0 (he i))
    nlinarith only [hh]
  exact ⟨h1, lt_of_lt_of_le (mul_pos ha h1) hm2⟩

/-- BB2 never exceeds BB1 when they are computed from the same nonzero gradient. -/
theorem bb2_le_bb1 {lam e : ι → ℝ} {a : ℝ} (ha : 0 < a)
    (he : ∀ i, 0 ≤ e i) (hlam : ∀ i, a ≤ lam i) (hE : 0 < mass e) :
    firstMoment lam e / secondMoment lam e ≤ mass e / firstMoment lam e := by
  obtain ⟨h1,h2⟩ := moments_pos ha he hlam hE
  apply (div_le_div_iff h2 h1).mpr
  nlinarith [moment_cauchy (lam := lam) he hE]

/-- The spectral weight representing a convex combination of the BB steps. -/
noncomputable def intervalWeight (lam e : ι → ℝ) (η : ℝ) (i : ι) : ℝ :=
  η * secondMoment lam e + (1 - η) * firstMoment lam e * lam i

/-- The exact quotient identity in the proof of Corollary 4.1. -/
theorem interval_representation {lam e : ι → ℝ} {η : ℝ}
    (h1 : firstMoment lam e ≠ 0) (h2 : secondMoment lam e ≠ 0) :
    alpha lam (intervalWeight lam e η) e =
      η * (mass e / firstMoment lam e) +
      (1 - η) * (firstMoment lam e / secondMoment lam e) := by
  have hnum : numerator (intervalWeight lam e η) e =
      η * secondMoment lam e * mass e + (1-η) * (firstMoment lam e)^2 := by
    unfold numerator intervalWeight mass
    simp_rw [add_mul, Finset.sum_add_distrib]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    unfold firstMoment
    ring
  have hden : denominator lam (intervalWeight lam e η) e =
      firstMoment lam e * secondMoment lam e := by
    unfold denominator intervalWeight
    simp_rw [add_mul, Finset.sum_add_distrib]
    have hterm : (∑ i, η * secondMoment lam e * lam i * e i) =
        η * secondMoment lam e * firstMoment lam e := by
      unfold firstMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hterm2 : (∑ i, (1 - η) * firstMoment lam e * lam i * lam i * e i) =
        (1 - η) * firstMoment lam e * secondMoment lam e := by
      unfold secondMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hterm, hterm2]
    ring
  unfold alpha
  rw [hnum,hden]
  field_simp
  <;> ring

/-- Every interpolating weight is strictly positive. -/
theorem interval_weight_pos {lam e : ι → ℝ} {a η : ℝ}
    (ha : 0 < a) (he : ∀ i, 0 ≤ e i) (hlam : ∀ i, a ≤ lam i)
    (hE : 0 < mass e) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (i : ι) :
    0 < intervalWeight lam e η i := by
  obtain ⟨h1,h2⟩ := moments_pos ha he hlam hE
  have hl : 0 < lam i := lt_of_lt_of_le ha (hlam i)
  unfold intervalWeight
  rcases eq_or_lt_of_le hη0 with hzero | hpos
  · rw [← hzero]
    simpa using mul_pos h1 hl
  · exact add_pos_of_pos_of_nonneg (mul_pos hpos h2)
      (mul_nonneg (mul_nonneg (by linarith) (le_of_lt h1)) (le_of_lt hl))

/-- The interpolating weights have condition number at most `b/a`.
The pointwise form avoids introducing a max/min operator on the finite set. -/
theorem interval_weight_condition {lam e : ι → ℝ} {a b η : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (he : ∀ i, 0 ≤ e i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (hE : 0 < mass e) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (i j : ι) :
    intervalWeight lam e η i ≤ (b/a) * intervalWeight lam e η j := by
  obtain ⟨h1,h2⟩ := moments_pos ha he hlama hE
  have hη : 0 ≤ 1 - η := by linarith
  have hd : 0 ≤ η * secondMoment lam e := mul_nonneg hη0 (le_of_lt h2)
  have hp : 0 ≤ (1-η) * firstMoment lam e := mul_nonneg hη (le_of_lt h1)
  have hcomp : a * lam i ≤ b * lam j := by
    calc
      a * lam i ≤ a * b := mul_le_mul_of_nonneg_left (hlamb i) (le_of_lt ha)
      _ ≤ b * lam j := by
        have hb : 0 ≤ b := le_trans (le_of_lt ha) hab
        nlinarith only [mul_le_mul_of_nonneg_left (hlama j) hb]
  have hprod := mul_le_mul_of_nonneg_left hcomp hp
  have hdprod := mul_le_mul_of_nonneg_right hab hd
  have heq : (b/a) * intervalWeight lam e η j =
      (b * intervalWeight lam e η j) / a := by ring
  rw [heq]
  apply (le_div_iff ha).mpr
  unfold intervalWeight
  nlinarith only [hprod, hdprod]

/-- Endpoint bounds need only hold on the support of the current energy. -/
theorem denominator_bounds_on_support {lam w e : ι → ℝ} {a b : ℝ}
    (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 ≤ w i)
    (hsupport : ∀ i, e i = 0 ∨ (a ≤ lam i ∧ lam i ≤ b)) :
    a * numerator w e ≤ denominator lam w e ∧
    denominator lam w e ≤ b * numerator w e := by
  constructor
  · unfold numerator denominator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases hsupport i with hz | ⟨hlo,_⟩
    · simp [hz]
    · nlinarith only [mul_le_mul_of_nonneg_left hlo (mul_nonneg (hw i) (he i))]
  · unfold numerator denominator
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases hsupport i with hz | ⟨_,hhi⟩
    · simp [hz]
    · nlinarith only [mul_le_mul_of_nonneg_left hhi (mul_nonneg (hw i) (he i))]

/-- The quotient range on an invariant spectral face. -/
theorem alpha_bounds_on_support {lam w e : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 ≤ w i)
    (hsupport : ∀ i, e i = 0 ∨ (a ≤ lam i ∧ lam i ≤ b))
    (hnum : 0 < numerator w e) :
    1/b ≤ alpha lam w e ∧ alpha lam w e ≤ 1/a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  obtain ⟨hlo,hhi⟩ := denominator_bounds_on_support he hw hsupport
  have hden : 0 < denominator lam w e := lt_of_lt_of_le (mul_pos ha hnum) hlo
  unfold alpha
  constructor
  · apply (div_le_div_iff hb hden).mpr
    nlinarith only [hhi]
  · apply (div_le_div_iff hden ha).mpr
    nlinarith only [hlo]

end BB.Spectral
