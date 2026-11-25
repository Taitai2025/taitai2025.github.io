import BB.Spectral
import BB.Hilbert

/-!
# Finite spectral rigidity at the midpoint

These results use the actual finite weighted multiplier and identify its
equality cases. They can be used by either the periodic-orbit argument or the
invariant-measure argument.
-/

noncomputable section

open scoped BigOperators

namespace BB

variable {ι : Type*} [Fintype ι]

theorem midpoint_spectral_multiplier_identity (lam : ι → ℝ) (i : ι)
    (a b : ℝ) (hsum : a + b ≠ 0) :
    multiplier lam ((a + b) / 2) i = (1 - 2 * lam i / (a + b)) ^ 2 := by
  unfold multiplier
  congr 1
  field_simp
  ring

theorem midpoint_spectral_multiplier_le (lam : ι → ℝ) (i : ι)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hi : a ≤ lam i ∧ lam i ≤ b) :
    multiplier lam ((a + b) / 2) i ≤ (rate a b) ^ 2 := by
  rw [midpoint_spectral_multiplier_identity lam i a b (ne_of_gt (by linarith))]
  simpa only [rate, add_comm b a] using
    midpoint_multiplier_le a b (lam i) ha hab hi.1 hi.2

theorem midpoint_spectral_multiplier_eq_iff (lam : ι → ℝ) (i : ι)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    multiplier lam ((a + b) / 2) i = (rate a b) ^ 2 ↔ lam i = a ∨ lam i = b := by
  rw [midpoint_spectral_multiplier_identity lam i a b (ne_of_gt (by linarith))]
  simpa only [rate, add_comm b a] using
    midpoint_multiplier_eq_iff a b (lam i) ha hab

theorem growth_sq_midpoint_le (lam w z : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hw : IsSimplex w) (hmean : mean lam z = (a + b) / 2) :
    growthSq lam w z ≤ (rate a b) ^ 2 := by
  calc
    growthSq lam w z = ∑ i, multiplier lam ((a + b) / 2) i * w i := by
      rw [growthSq, hmean]
    _ ≤ ∑ i, (rate a b) ^ 2 * w i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right
        (midpoint_spectral_multiplier_le lam i a b ha hab (hlam i)) (hw.1 i))
    _ = (rate a b) ^ 2 := by rw [← Finset.mul_sum, hw.2, mul_one]

/-- Equality of midpoint growth holds exactly when every nonzero coordinate
belongs to one of the two extreme eigenspaces. -/
theorem growth_sq_midpoint_eq_iff (lam w z : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hw : IsSimplex w) (hmean : mean lam z = (a + b) / 2) :
    growthSq lam w z = (rate a b) ^ 2 ↔
      ∀ i, w i ≠ 0 → lam i = a ∨ lam i = b := by
  have hgap (i : ι) : 0 ≤ ((rate a b) ^ 2 - multiplier lam ((a + b) / 2) i) * w i :=
    mul_nonneg (sub_nonneg.mpr (midpoint_spectral_multiplier_le lam i a b ha hab (hlam i)))
      (hw.1 i)
  constructor
  · intro heq i hwi
    have hsum : (∑ j, ((rate a b) ^ 2 - multiplier lam ((a + b) / 2) j) * w j) = 0 := by
      simp_rw [sub_mul]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2, mul_one]
      have hR : (∑ j, multiplier lam ((a + b) / 2) j * w j) = (rate a b) ^ 2 := by
        simpa only [growthSq, hmean] using heq
      rw [hR, sub_self]
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hgap j)).mp hsum i
      (Finset.mem_univ i)
    have hmult : multiplier lam ((a + b) / 2) i = (rate a b) ^ 2 := by
      have := (mul_eq_zero.mp hi0).resolve_right hwi
      linarith
    exact (midpoint_spectral_multiplier_eq_iff lam i a b ha hab).mp hmult
  · intro hsupport
    calc
      growthSq lam w z = ∑ i, (rate a b) ^ 2 * w i := by
        unfold growthSq
        rw [hmean]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hwi : w i = 0
        · simp only [hwi, mul_zero]
        · rw [(midpoint_spectral_multiplier_eq_iff lam i a b ha hab).mpr (hsupport i hwi)]
      _ = (rate a b) ^ 2 := by rw [← Finset.mul_sum, hw.2, mul_one]

/-- A probability vector supported on two distinct coordinates and having
midpoint mean assigns mass one half to each. -/
theorem endpoint_balance_of_simplex_mean (lam w : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hw : IsSimplex w) (hmean : mean lam w = (a + b) / 2)
    (hsupport : ∀ i, i ≠ lo → i ≠ hi → w i = 0) :
    w lo = 1 / 2 ∧ w hi = 1 / 2 := by
  have hne : lo ≠ hi := by
    intro h
    have : a = b := hlo.symm.trans (h ▸ hhi)
    linarith
  have hsum : (∑ i, w i) = w lo + w hi :=
    Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
      (fun i _ hn => hsupport i hn.1 hn.2)
  have hm : (∑ i, lam i * w i) = lam lo * w lo + lam hi * w hi :=
    Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
      (fun i _ hn => by rw [hsupport i hn.1 hn.2, mul_zero])
  have htotal : w lo + w hi = 1 := by rw [← hsum, hw.2]
  have hlinear : a * w lo + b * w hi = (a + b) / 2 := by
    simpa only [mean, hm, hlo, hhi] using hmean
  have htotalb : b * w lo + b * w hi = b := by
    rw [← mul_add, htotal, mul_one]
  have hprod : (b - a) * (w lo - 1 / 2) = 0 := by
    nlinarith only [hlinear, htotalb]
  have hwlo : w lo = 1 / 2 := by
    have := (mul_eq_zero.mp hprod).resolve_left (sub_pos.mpr hab).ne'
    linarith
  exact ⟨hwlo, by linarith⟩

end BB
