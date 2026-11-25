import BB.Sharpness

noncomputable section
namespace BB.Numerical

open BB.Spectral BB.Sharpness
open scoped BigOperators

abbrev QPoint := ℚ × ℚ

def qAlpha (g : QPoint) : ℚ := (g.1^2+g.2^2)/(g.1^2+10*g.2^2)
def qUpdate (α : ℚ) (g : QPoint) : QPoint := ((1-α)*g.1,(1-10*α)*g.2)
def qState : ℕ → QPoint × QPoint
  | 0 => ((1,2),(36/41,-18/41))
  | k+1 => ((qState k).2,qUpdate (qAlpha (qState k).1) (qState k).2)

def qGradient (k : ℕ) : QPoint := (qState k).2
def qAlphaAt (k : ℕ) : ℚ := qAlpha (qState k).1
def qObjective (g : QPoint) : ℚ := (g.1^2+g.2^2/10)/2
def qNormSq (g : QPoint) : ℚ := g.1^2+g.2^2
def qEnergyPower (g : QPoint) : ℚ := g.1^20*g.2^2
def qPosition (g : QPoint) : QPoint := (g.1,g.2/10)

def realPair (g : QPoint) : Fin 2 → ℝ := ![(g.1:ℝ),(g.2:ℝ)]
def realGradient (k : ℕ) : Fin 2 → ℝ := realPair (qGradient k)
def realState (k : ℕ) : State (Fin 2) := (realPair (qState k).1,realPair (qState k).2)
def alpha (k : ℕ) : ℝ := (qAlphaAt k:ℝ)
def objective (k : ℕ) : ℝ := (qObjective (qGradient k):ℝ)
def gradientNorm (k : ℕ) : ℝ := twoNorm (realGradient k)
def energy (k : ℕ) : ℝ :=
  |realGradient k 0|^(20/11:ℝ) * |realGradient k 1|^(2/11:ℝ)
def energyRatio (k : ℕ) : ℝ := energy (k+1)/energy k
def gradientRatio (k : ℕ) : ℝ := gradientNorm (k+1)/gradientNorm k
def objectiveRatio (k : ℕ) : ℝ := objective (k+1)/objective k

theorem realPair_alpha (g : QPoint) :
    vectorAlpha (twoSpectrum 1 10) (twoWeights 1 1) (realPair g) = (qAlpha g:ℝ) := by
  simp [vectorAlpha,quadraticForm,twoSpectrum,twoWeights,realPair,qAlpha,Fin.sum_univ_two]

theorem realPair_update (α : ℚ) (g : QPoint) :
    realPair (qUpdate α g) = diagonalStep (twoSpectrum 1 10) (α:ℝ) (realPair g) := by
  funext i
  fin_cases i <;> simp [realPair,qUpdate,diagonalStep,twoSpectrum,mul_comm]

/-- Every row belongs to one exact rational delayed BB1 orbit. -/
theorem actual_state_recurrence (k : ℕ) :
    realState (k+1) = stateMap (twoSpectrum 1 10) (twoWeights 1 1) (realState k) := by
  unfold realState stateMap
  rw [qState]
  apply Prod.ext
  · rfl
  · change realPair (qUpdate (qAlpha (qState k).1) (qState k).2) =
      diagonalStep (twoSpectrum 1 10)
        (vectorAlpha (twoSpectrum 1 10) (twoWeights 1 1) (realPair (qState k).1))
        (realPair (qState k).2)
    rw [realPair_alpha,realPair_update]

theorem actual_alpha (k : ℕ) :
    alpha k = vectorAlpha (twoSpectrum 1 10) (twoWeights 1 1) (realState k).1 := by
  exact (realPair_alpha (qState k).1).symm

/-- The displayed warm-up pair is itself a genuine matched BB1 update. -/
theorem warmup_exact : qAlpha ((1,2):QPoint)=5/41 ∧
    qUpdate (5/41) ((1,2):QPoint)=qGradient 0 := by
  norm_num [qAlpha,qUpdate,qGradient,qState]

theorem warmup_secant : qPosition (qGradient 0)-qPosition ((1,2):QPoint) =
    (-(5/41):ℚ) • ((1,2):QPoint) := by
  apply Prod.ext <;> norm_num [qPosition,qGradient,qState]

theorem objective_is_quadratic (g : QPoint) : qObjective g =
    ((qPosition g).1^2+10*(qPosition g).2^2)/2 := by
  unfold qPosition qObjective
  ring

theorem objective_formula (k : ℕ) :
    objective k = ((realGradient k 0)^2+(realGradient k 1)^2/10)/2 := by
  simp [objective,qObjective,realGradient,realPair]

theorem gradientNorm_is_euclidean (k : ℕ) :
    gradientNorm k = ‖(EuclideanSpace.equiv (Fin 2) ℝ).symm (realGradient k)‖ :=
  twoNorm_eq_euclidean_norm _

theorem gradientNorm_nonneg (k : ℕ) : 0 ≤ gradientNorm k := Real.sqrt_nonneg _

theorem gradientNorm_sq (k : ℕ) : (gradientNorm k)^2=(qNormSq (qGradient k):ℝ) := by
  unfold gradientNorm twoNorm
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))]
  simp [realGradient,realPair,qNormSq]

theorem energy_nonneg (k : ℕ) : 0 ≤ energy k :=
  mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (abs_nonneg _) _)

/-- Fractional powers are reduced exactly to an eleventh-power rational identity. -/
theorem energy_power (k : ℕ) : (energy k)^11=(qEnergyPower (qGradient k):ℝ) := by
  have hp (x : ℝ) : (|x|^(20/11:ℝ))^11=x^20 := by
    rw [← Real.rpow_mul_natCast (abs_nonneg x)]
    norm_num
    rw [show (20:ℝ)=(20:ℕ) by norm_num,Real.rpow_natCast]
    exact (show Even (20:ℕ) by decide).pow_abs x
  have hq (y : ℝ) : (|y|^(2/11:ℝ))^11=y^2 := by
    rw [← Real.rpow_mul_natCast (abs_nonneg y)]
    norm_num [sq_abs]
  unfold energy
  rw [mul_pow,hp,hq]
  simp [realGradient,realPair,qEnergyPower]

theorem energyRatio_nonneg (k : ℕ) : 0 ≤ energyRatio k :=
  div_nonneg (energy_nonneg _) (energy_nonneg _)

theorem energyRatio_power (k : ℕ) : (energyRatio k)^11=
    (qEnergyPower (qGradient (k+1))/qEnergyPower (qGradient k):ℚ) := by
  simp only [energyRatio,div_pow,energy_power,Rat.cast_div]

theorem gradientRatio_nonneg (k : ℕ) : 0 ≤ gradientRatio k :=
  div_nonneg (gradientNorm_nonneg _) (gradientNorm_nonneg _)

theorem gradientRatio_sq (k : ℕ) : (gradientRatio k)^2=
    (qNormSq (qGradient (k+1))/qNormSq (qGradient k):ℚ) := by
  simp only [gradientRatio,div_pow,gradientNorm_sq,Rat.cast_div]

/-- A strict half-unit enclosure certifies rounding to the displayed last digit. -/
def Rounded (v : ℝ) (center radius : ℚ) : Prop :=
  ((center-radius:ℚ):ℝ) < v ∧ v < ((center+radius:ℚ):ℝ)

theorem rounded_abs {v : ℝ} {center radius : ℚ} (h : Rounded v center radius) :
    |v-(center:ℝ)| < (radius:ℝ) := by
  have hl := h.1
  have hu := h.2
  push_cast at hl hu
  exact abs_lt.mpr ⟨by linarith only [hl],by linarith only [hu]⟩

/-- Kernel-checkable rational power inequalities certify irrational decimal entries. -/
theorem powered_rounding (n : ℕ) {v : ℝ} {value center radius : ℚ}
    (hv : 0 ≤ v) (hpow : v^n=(value:ℝ))
    (hlo : 0 ≤ center-radius) (hhi : 0 ≤ center+radius)
    (hloP : (center-radius)^n < value) (hhiP : value < (center+radius)^n) :
    Rounded v center radius := by
  have hl : (((center-radius:ℚ):ℝ))^n < v^n := by
    rw [hpow]
    exact_mod_cast hloP
  have hu : v^n < (((center+radius:ℚ):ℝ))^n := by
    rw [hpow]
    exact_mod_cast hhiP
  constructor
  · by_contra hh
    have hm := pow_le_pow_left hv (le_of_not_gt hh) n
    exact (not_lt_of_ge hm) hl
  · by_contra hh
    have hn : 0 ≤ ((center+radius:ℚ):ℝ) := by exact_mod_cast hhi
    have hm := pow_le_pow_left hn (le_of_not_gt hh) n
    exact (not_lt_of_ge hm) hu

theorem contraction_constant : (BB.endpointRate 1 10)^2=(81/121:ℝ) := by
  norm_num [BB.endpointRate]

end BB.Numerical
