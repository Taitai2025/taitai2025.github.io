import BB.Endpoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite spectral state and its exact update

Every result is over real coordinates and arbitrary finite index types.
The delayed state uses two independent simplex points; no matched-start
assumption is silently imposed.
-/

namespace BB
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def IsSimplex (w : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1

def mean (lam w : ι → ℝ) : ℝ := ∑ i, lam i * w i

def multiplier (lam : ι → ℝ) (u : ℝ) (i : ι) : ℝ := (1 - lam i / u)^2

def growthSq (lam w z : ι → ℝ) : ℝ :=
  ∑ i, multiplier lam (mean lam z) i * w i

def weightUpdate (lam w z : ι → ℝ) (i : ι) : ℝ :=
  multiplier lam (mean lam z) i * w i / growthSq lam w z

def gradientUpdate (lam : ι → ℝ) (α : ℝ) (g : ι → ℝ) (i : ι) : ℝ :=
  (1 - α * lam i) * g i

def energy (g : ι → ℝ) : ℝ := ∑ i, (g i)^2

def energyWeights (g : ι → ℝ) (i : ι) : ℝ := (g i)^2 / energy g

theorem energy_nonneg (g : ι → ℝ) : 0 ≤ energy g :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (g i))

theorem energy_pos {g : ι → ℝ} (hg : ∃ i, g i ≠ 0) : 0 < energy g := by
  obtain ⟨i, hi⟩ := hg
  exact Finset.sum_pos' (fun j _ => sq_nonneg (g j))
    ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩

theorem energy_weights_simplex {g : ι → ℝ} (hg : 0 < energy g) :
    IsSimplex (energyWeights g) := by
  constructor
  · intro i
    exact div_nonneg (sq_nonneg _) (le_of_lt hg)
  · unfold energyWeights
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hg)

theorem mean_lower {lam w : ι → ℝ} {a : ℝ}
    (hw : IsSimplex w) (hlam : ∀ i, a ≤ lam i) : a ≤ mean lam w := by
  calc
    a = ∑ i, a * w i := by rw [← Finset.mul_sum, hw.2, mul_one]
    _ ≤ ∑ i, lam i * w i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hlam i) (hw.1 i)

theorem mean_upper {lam w : ι → ℝ} {b : ℝ}
    (hw : IsSimplex w) (hlam : ∀ i, lam i ≤ b) : mean lam w ≤ b := by
  calc
    (∑ i, lam i * w i) ≤ ∑ i, b * w i := Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_right (hlam i) (hw.1 i)
    _ = b := by rw [← Finset.mul_sum, hw.2, mul_one]

theorem mean_strict_lower {lam w : ι → ℝ} {a : ℝ} {j : ι}
    (hw : IsSimplex w) (hlam : ∀ i, a ≤ lam i)
    (hj : a < lam j) (hwj : 0 < w j) : a < mean lam w := by
  have hsum : 0 < ∑ i, (lam i - a) * w i :=
    Finset.sum_pos' (fun i _ => mul_nonneg (sub_nonneg.mpr (hlam i)) (hw.1 i))
      ⟨j, Finset.mem_univ j, mul_pos (sub_pos.mpr hj) hwj⟩
  have hid : (∑ i, (lam i - a) * w i) = mean lam w - a := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2, mul_one]
    rfl
  rw [hid] at hsum
  linarith

theorem mean_strict_upper {lam w : ι → ℝ} {b : ℝ} {j : ι}
    (hw : IsSimplex w) (hlam : ∀ i, lam i ≤ b)
    (hj : lam j < b) (hwj : 0 < w j) : mean lam w < b := by
  have hsum : 0 < ∑ i, (b - lam i) * w i :=
    Finset.sum_pos' (fun i _ => mul_nonneg (sub_nonneg.mpr (hlam i)) (hw.1 i))
      ⟨j, Finset.mem_univ j, mul_pos (sub_pos.mpr hj) hwj⟩
  have hid : (∑ i, (b - lam i) * w i) = b - mean lam w := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2, mul_one]
    rfl
  rw [hid] at hsum
  linarith

theorem growth_sq_nonneg {lam w z : ι → ℝ} (hw : IsSimplex w) :
    0 ≤ growthSq lam w z :=
  Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (hw.1 i)

theorem weight_update_simplex {lam w z : ι → ℝ}
    (hw : IsSimplex w) (hR : 0 < growthSq lam w z) :
    IsSimplex (weightUpdate lam w z) := by
  constructor
  · intro i
    exact div_nonneg (mul_nonneg (sq_nonneg _) (hw.1 i)) (le_of_lt hR)
  · unfold weightUpdate
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt hR)

theorem weight_update_zero {lam w z : ι → ℝ} {i : ι} (hi : w i = 0) :
    weightUpdate lam w z i = 0 := by
  simp [weightUpdate, hi]

theorem gradient_update_zero {lam g : ι → ℝ} {α : ℝ} {i : ι} (hi : g i = 0) :
    gradientUpdate lam α g i = 0 := by simp [gradientUpdate, hi]

theorem energy_update_factorization {lam g z : ι → ℝ}
    (hg : 0 < energy g) :
    energy (gradientUpdate lam (1 / mean lam z) g) =
      growthSq lam (energyWeights g) z * energy g := by
  unfold energy gradientUpdate growthSq multiplier energyWeights
  simp only [energy]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hge : (∑ i, (g i)^2) ≠ 0 := ne_of_gt hg
  field_simp
  ring

theorem energy_weights_update {lam g z : ι → ℝ}
    (hg : 0 < energy g) :
    energyWeights (gradientUpdate lam (1 / mean lam z) g) =
      weightUpdate lam (energyWeights g) z := by
  funext i
  unfold energyWeights
  rw [energy_update_factorization hg]
  unfold gradientUpdate weightUpdate multiplier energyWeights
  field_simp
  ring

/-- A normalized diagonal BB state with positive endpoint masses has a mean
strictly between the endpoints and a positive squared norm multiplier. -/
theorem endpoint_state_regular {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hw : IsSimplex w) (hz : IsSimplex z)
    (hwlo : 0 < w lo) (hzlo : 0 < z lo) (hzhi : 0 < z hi) :
    a < mean lam z ∧ mean lam z < b ∧ 0 < growthSq lam w z := by
  have hu : a < mean lam z := mean_strict_lower hz (fun i => (hlam i).1)
    (by simpa only [hhi] using hab) hzhi
  have hv : mean lam z < b := mean_strict_upper hz (fun i => (hlam i).2)
    (by simpa only [hlo] using hab) hzlo
  refine ⟨hu, hv, ?_⟩
  apply Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (hw.1 i))
  refine ⟨lo, Finset.mem_univ lo, mul_pos ?_ hwlo⟩
  apply sq_pos_of_ne_zero
  rw [hlo]
  have hum : 0 < mean lam z := lt_trans ha hu
  have hal : a / mean lam z < 1 := (div_lt_one hum).mpr hu
  linarith

/-- `lem:cohomology` for the actual finite-dimensional simplex update. -/
theorem spectral_cohomology {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hw : IsSimplex w) (hz : IsSimplex z)
    (hwlo : 0 < w lo) (hwhi : 0 < w hi)
    (hzlo : 0 < z lo) (hzhi : 0 < z hi) :
    Real.log (Real.sqrt (growthSq lam w z)) =
      Real.log (rate a b) - endpointDefect a b (mean lam z) +
        endpointPotential a b (weightUpdate lam w z lo) (weightUpdate lam w z hi) -
          endpointPotential a b (w lo) (w hi) := by
  obtain ⟨hau, hub, hR⟩ := endpoint_state_regular ha hab hlo hhi hlam hw hz hwlo hzlo hzhi
  have hu : mean lam z ≠ 0 := ne_of_gt (lt_trans ha hau)
  have h1 : (1 - a / mean lam z)^2 = ((mean lam z - a) / mean lam z)^2 := by
    congr 1
    field_simp
  have h2 : (1 - b / mean lam z)^2 = ((b - mean lam z) / mean lam z)^2 := by
    field_simp
    ring
  rw [Real.log_sqrt (le_of_lt hR)]
  unfold weightUpdate multiplier
  rw [hlo, hhi, h1, h2]
  exact endpoint_cohomology ha hau hub hwlo hwhi hR

end
end BB
