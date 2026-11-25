import BB.Sharpness

noncomputable section
namespace BB.Divergence

open BB.Spectral BB.Sharpness
open Filter

/-- The explicit divergent gradient sequence from the final manuscript. -/
def gradient (k : ℕ) : Fin 2 → ℝ := ![(1/2:ℝ)^k, Real.sqrt 8 * (-4:ℝ)^k]

/-- The first weight is matched; its value equals the weight at time one. -/
def weight (k : ℕ) : Fin 2 → ℝ := ![1,if k=0 then (1/64:ℝ) else (1/64:ℝ)^k]

def state (k : ℕ) : State (Fin 2) := (gradient (k-1),gradient k)

theorem weight_positive (k : ℕ) (i : Fin 2) : 0 < weight k i := by
  fin_cases i
  · norm_num [weight]
  · change 0 < (if k=0 then (1/64:ℝ) else (1/64:ℝ)^k)
    split_ifs <;> positivity

/-- The crucial exact weighted energy ratio for every step after initialization. -/
theorem energy_ratio_successor (k : ℕ) :
    (1/64:ℝ)^(k+1)*(Real.sqrt 8*(-4:ℝ)^k)^2 =
      (1/8:ℝ)*((1/2:ℝ)^k)^2 := by
  have hneg : ((-4:ℝ)^k)^2 = (16:ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  have hhalf : ((1/2:ℝ)^k)^2 = (1/4:ℝ)^k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul]
    norm_num
  rw [mul_pow,Real.sq_sqrt (by norm_num : (0:ℝ)≤8),hneg,hhalf,pow_succ]
  calc
    ((1/64:ℝ)^k*(1/64))*(8*16^k) = (1/8:ℝ)*((1/64:ℝ)^k*16^k) := by ring
    _ = (1/8:ℝ)*(((1/64:ℝ)*16)^k) := by rw [←mul_pow]
    _ = _ := by norm_num

/-- A fixed ratio 1/8 on spectrum {1,10} gives the exact step 1/2. -/
theorem quotient_from_ratio {w x y : ℝ} (hx : x ≠ 0) (hbal : w*y^2=(1/8:ℝ)*x^2) :
    vectorAlpha (twoSpectrum 1 10) (twoWeights 1 w) ![x,y] = (1/2:ℝ) := by
  simp only [vectorAlpha, quadraticForm, Fin.sum_univ_two, twoSpectrum,twoWeights,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons,one_mul]
  rw [show w*10*y^2=10*(w*y^2) by ring,hbal]
  field_simp
  <;> ring

/-- Every quotient, including matched time zero, equals 1/2. -/
theorem quotient_constant (k : ℕ) :
    vectorAlpha (twoSpectrum 1 10) (weight k) (gradient (k-1)) = (1/2:ℝ) := by
  cases k with
  | zero =>
    simp only [weight,gradient,Nat.zero_sub,if_pos rfl,pow_zero,mul_one]
    apply quotient_from_ratio (by norm_num)
    rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤8)]
    norm_num
  | succ k =>
    simp only [weight, gradient, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
    apply quotient_from_ratio (pow_ne_zero _ (by norm_num))
    exact energy_ratio_successor k

/-- The displayed gradient sequence follows the actual gradient recurrence. -/
theorem gradient_step (k : ℕ) :
    diagonalStep (twoSpectrum 1 10) (1/2) (gradient k) = gradient (k+1) := by
  funext i
  fin_cases i
  · change (1-(1/2:ℝ)*1)*(1/2:ℝ)^k = (1/2:ℝ)^(k+1)
    rw [pow_succ]
    ring
  · change (1-(1/2:ℝ)*10)*(Real.sqrt 8*(-4:ℝ)^k) = Real.sqrt 8*(-4:ℝ)^(k+1)
    rw [pow_succ]
    ring

/-- Hence the example is a delayed weighted BB trajectory, with matched startup. -/
theorem state_recurrence (k : ℕ) :
    stateMap (twoSpectrum 1 10) (weight k) (state k) = state (k+1) := by
  unfold state stateMap
  rw [quotient_constant,gradient_step]
  simp

@[simp] theorem state_initial : state 0 = (![1,Real.sqrt 8],![1,Real.sqrt 8]) := by
  simp [state,gradient]

/-- Euclidean norm dominates either coordinate. -/
theorem abs_snd_le_twoNorm (g : Fin 2 → ℝ) : |g 1| ≤ twoNorm g := by
  apply (Real.le_sqrt (abs_nonneg _) (add_nonneg (sq_nonneg _) (sq_nonneg _))).mpr
  rw [sq_abs]
  linarith only [sq_nonneg (g 0)]

theorem gradient_norm_lower (k : ℕ) : (4:ℝ)^k*Real.sqrt 8 ≤ twoNorm (gradient k) := by
  have h := abs_snd_le_twoNorm (gradient k)
  change |Real.sqrt 8 * (-4:ℝ)^k| ≤ twoNorm (gradient k) at h
  rw [abs_mul,abs_of_nonneg (Real.sqrt_nonneg 8),abs_pow] at h
  norm_num at h
  simpa only [mul_comm] using h

/-- The actual Euclidean gradient norms tend to infinity. -/
theorem gradient_norm_tendsto_atTop : Tendsto (fun k => twoNorm (gradient k)) atTop atTop := by
  apply Filter.tendsto_atTop_mono gradient_norm_lower
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<4)).atTop_mul_const
    (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<8))

/-- At every positive time the ratio of largest to smallest weight is exactly 64^k. -/
theorem weight_ratio_successor (k : ℕ) : weight (k+1) 0 / weight (k+1) 1 = (64:ℝ)^(k+1) := by
  simp only [weight, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]
  rw [←one_div_pow]
  norm_num

/-- The weights are individually positive but their ratios have no uniform bound. -/
theorem weight_ratio_tendsto_atTop :
    Tendsto (fun k => weight (k+1) 0 / weight (k+1) 1) atTop atTop := by
  simp only [weight_ratio_successor,pow_succ]
  exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<64)).atTop_mul_const
    (by norm_num : (0:ℝ)<64)

/-- Every step still lies in the inverse spectral interval. -/
theorem constant_step_in_bounds : (1/10:ℝ) ≤ 1/2 ∧ (1/2:ℝ) ≤ 1 := by norm_num

end BB.Divergence
