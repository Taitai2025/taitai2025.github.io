import BB.ScalarStep
import BB.Endpoint
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

namespace BB.Sharpness

open BB.Spectral
open scoped BigOperators

/-- A two-dimensional diagonal Hessian with the prescribed spectral endpoints. -/
def twoSpectrum (a b : ℝ) : Fin 2 → ℝ := ![a,b]

/-- Positive diagonal weights on the two endpoint eigenspaces. -/
def twoWeights (wa wb : ℝ) : Fin 2 → ℝ := ![wa,wb]

/-- The balanced endpoint orbit in physical gradient coordinates. -/
def balancedGradient (a b x y : ℝ) (k : ℕ) : Fin 2 → ℝ :=
  ![BB.endpointRate a b ^ k * x, (-BB.endpointRate a b) ^ k * y]

/-- Matched initialization is encoded by repeating gradient zero as the preceding gradient. -/
def balancedState (a b x y : ℝ) (k : ℕ) : State (Fin 2) :=
  (balancedGradient a b x y (k-1), balancedGradient a b x y k)

/-- Explicit Euclidean norm in two coordinates. -/
def twoNorm (g : Fin 2 → ℝ) : ℝ := Real.sqrt ((g 0)^2+(g 1)^2)

/-- A positive pair of weights always admits a nonzero balanced initial gradient. -/
theorem exists_balanced_components {wa wb : ℝ} (hwa : 0 < wa) (hwb : 0 < wb) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧ wa*x^2 = wb*y^2 := by
  refine ⟨Real.sqrt wb, Real.sqrt wa, Real.sqrt_pos.mpr hwb, Real.sqrt_pos.mpr hwa, ?_⟩
  rw [Real.sq_sqrt hwb.le, Real.sq_sqrt hwa.le]
  ring

/-- The two weighted endpoint energies stay equal at every time. -/
theorem balanced_energy {a b x y wa wb : ℝ} (hbal : wa*x^2=wb*y^2) (k : ℕ) :
    wa * (balancedGradient a b x y k 0)^2 = wb * (balancedGradient a b x y k 1)^2 := by
  have hneg : ((-BB.endpointRate a b)^k)^2 = (BB.endpointRate a b^k)^2 := by
    rw [← sq_abs, abs_pow, abs_neg, ← abs_pow, sq_abs]
  simp only [balancedGradient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    mul_pow, hneg]
  calc
    wa * ((BB.endpointRate a b ^ k) ^ 2 * x ^ 2) =
      (BB.endpointRate a b ^ k)^2 * (wa*x^2) := by ring
    _ = (BB.endpointRate a b ^ k)^2 * (wb*y^2) := by rw [hbal]
    _ = _ := by ring


/-- A balanced weighted two-endpoint vector has the fixed midpoint reciprocal step. -/
theorem vectorAlpha_two_balanced {a b wa wb x y : ℝ}
    (ha : 0 < a) (hab : a < b) (hwa : 0 < wa) (hx : 0 < x)
    (hbal : wa*x^2=wb*y^2) :
    vectorAlpha (twoSpectrum a b) (twoWeights wa wb) ![x,y] = 2/(a+b) := by
  have hE : 0 < wa*x^2 := mul_pos hwa (sq_pos_of_pos hx)
  have hsum : 0 < a+b := by linarith only [ha,hab]
  have hden : wa*a*x^2 + wb*b*y^2 = (a+b)*(wa*x^2) := by
    calc
      wa*a*x^2 + wb*b*y^2 = a*(wa*x^2)+b*(wb*y^2) := by ring
      _ = (a+b)*(wa*x^2) := by rw [← hbal]; ring
  simp only [vectorAlpha, quadraticForm, Fin.sum_univ_two, twoSpectrum, twoWeights,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [hden, ← hbal]
  field_simp
  <;> ring

/-- The weighted quotient is constant along the explicit balanced orbit. -/
theorem balanced_quotient {a b wa wb x y : ℝ}
    (ha : 0 < a) (hab : a < b) (hwa : 0 < wa) (hx : 0 < x)
    (hbal : wa*x^2=wb*y^2) (k : ℕ) :
    vectorAlpha (twoSpectrum a b) (twoWeights wa wb) (balancedGradient a b x y k) = 2/(a+b) := by
  apply vectorAlpha_two_balanced ha hab hwa
    (mul_pos (pow_pos (BB.endpointRate_pos ha hab) k) hx)
  exact balanced_energy hbal k

theorem midpoint_multipliers {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    1-(2/(a+b))*a=BB.endpointRate a b ∧
    1-(2/(a+b))*b= -BB.endpointRate a b := by
  have hs : a+b ≠ 0 := ne_of_gt (by linarith only [ha,hab])
  have hs' : b+a ≠ 0 := ne_of_gt (by linarith only [ha,hab])
  unfold BB.endpointRate
  constructor <;> field_simp <;> ring

/-- An actual gradient update maps the explicit balanced gradient to the next one. -/
theorem balanced_gradient_step {a b x y : ℝ} (ha : 0 < a) (hab : a < b) (k : ℕ) :
    diagonalStep (twoSpectrum a b) (2/(a+b)) (balancedGradient a b x y k) =
      balancedGradient a b x y (k+1) := by
  obtain ⟨hlo,hhi⟩ := midpoint_multipliers ha hab
  funext i
  fin_cases i
  · change (1-(2/(a+b))*a)*(BB.endpointRate a b^k*x) = BB.endpointRate a b^(k+1)*x
    rw [hlo,pow_succ]
    ring
  · change (1-(2/(a+b))*b)*((-BB.endpointRate a b)^k*y) = (-BB.endpointRate a b)^(k+1)*y
    rw [hhi,pow_succ]
    ring

/-- The explicit orbit is the actual delayed weighted BB iteration, including matched startup. -/
theorem balanced_state_recurrence {a b wa wb x y : ℝ}
    (ha : 0 < a) (hab : a < b) (hwa : 0 < wa) (hx : 0 < x)
    (hbal : wa*x^2=wb*y^2) (k : ℕ) :
    stateMap (twoSpectrum a b) (twoWeights wa wb) (balancedState a b x y k) =
      balancedState a b x y (k+1) := by
  unfold balancedState stateMap
  rw [balanced_quotient ha hab hwa hx hbal, balanced_gradient_step ha hab]
  simp

@[simp] theorem balanced_state_initial (a b x y : ℝ) :
    balancedState a b x y 0 = (![x,y],![x,y]) := by
  simp [balancedState,balancedGradient]

/-- `twoNorm` is exactly the Euclidean norm, not the default sup norm on function coordinates. -/
theorem twoNorm_eq_euclidean_norm (g : Fin 2 → ℝ) :
    twoNorm g = ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm g‖ := by
  rw [EuclideanSpace.norm_eq]
  simp only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]
  rfl

/-- Euclidean norm of the balanced gradient, exactly at every finite time. -/
theorem balanced_norm {a b x y : ℝ} (ha : 0 < a) (hab : a < b) (k : ℕ) :
    twoNorm (balancedGradient a b x y k) =
      BB.endpointRate a b ^ k * twoNorm (balancedGradient a b x y 0) := by
  have hneg : ((-BB.endpointRate a b)^k)^2 = (BB.endpointRate a b^k)^2 := by
    rw [← sq_abs, abs_pow, abs_neg, ← abs_pow, sq_abs]
  unfold twoNorm
  simp only [balancedGradient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    pow_zero, one_mul]
  rw [mul_pow,mul_pow,hneg]
  rw [show (BB.endpointRate a b^k)^2*x^2+(BB.endpointRate a b^k)^2*y^2 =
    (BB.endpointRate a b^k)^2*(x^2+y^2) by ring, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (pow_nonneg (BB.endpointRate_pos ha hab).le k)]

/-- A strictly smaller exponential factor cannot have any finite prefactor on the balanced orbit. -/
theorem no_smaller_uniform_factor {a b x y r : ℝ} (ha : 0 < a) (hab : a < b)
    (hx : 0 < x) (hr : 0 ≤ r) (hrc : r < BB.endpointRate a b) :
    ¬ ∃ K : ℝ, ∀ k : ℕ, twoNorm (balancedGradient a b x y k) ≤
      K * r^k * twoNorm (balancedGradient a b x y 0) := by
  have hG : 0 < twoNorm (balancedGradient a b x y 0) := by
    unfold twoNorm
    simp only [balancedGradient, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      pow_zero,one_mul]
    exact Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg y))
  rintro ⟨K,hK⟩
  by_cases hr0 : r=0
  · have h := hK 1
    rw [balanced_norm ha hab, hr0] at h
    norm_num at h
    exact (not_le_of_gt (mul_pos (BB.endpointRate_pos ha hab) hG)) h
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt K ((one_lt_div hrp).2 hrc)
  have h := hK k
  rw [balanced_norm ha hab] at h
  have hpow : BB.endpointRate a b^k ≤ K*r^k := (mul_le_mul_right hG).mp h
  have hdiv : (BB.endpointRate a b/r)^k ≤ K := by
    rw [div_pow]
    exact (div_le_iff (pow_pos hrp k)).2 hpow
  exact (not_lt_of_ge hdiv) hk

/-- The manuscript's weighted endpoint example exists for every fixed positive diagonal weight. -/
theorem sharp_weighted_example {a b wa wb : ℝ}
    (ha : 0 < a) (hab : a < b) (hwa : 0 < wa) (hwb : 0 < wb) :
    ∃ x y : ℝ, 0 < x ∧ 0 < y ∧
      (∀ k, stateMap (twoSpectrum a b) (twoWeights wa wb) (balancedState a b x y k) =
        balancedState a b x y (k+1)) ∧
      (∀ k, twoNorm (balancedGradient a b x y k) =
        BB.endpointRate a b^k * twoNorm (balancedGradient a b x y 0)) ∧
      (∀ r : ℝ, 0 ≤ r → r < BB.endpointRate a b →
        ¬ ∃ K : ℝ, ∀ k : ℕ, twoNorm (balancedGradient a b x y k) ≤
          K*r^k*twoNorm (balancedGradient a b x y 0)) := by
  obtain ⟨x,y,hx,hy,hbal⟩ := exists_balanced_components hwa hwb
  exact ⟨x,y,hx,hy,balanced_state_recurrence ha hab hwa hx hbal,
    balanced_norm ha hab, fun _ hr hrc => no_smaller_uniform_factor ha hab hx hr hrc⟩

end BB.Sharpness
