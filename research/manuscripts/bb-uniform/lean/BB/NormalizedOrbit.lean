import BB.NormalizedDynamics
import BB.ScalarSupport
import BB.BlockNorms

set_option autoImplicit false

noncomputable section
namespace BB.Baseline
open scoped BigOperators
open BB.Spectral

variable {ι : Type*} [Fintype ι]

def spectralNorm (u : ι → ℝ) : ℝ := Real.sqrt (squaredMass u)

theorem squaredMass_nonneg (u : ι → ℝ) : 0 ≤ squaredMass u :=
  Finset.sum_nonneg (fun i _ => sq_nonneg (u i))

@[simp] theorem squaredMass_zero : squaredMass (0 : ι → ℝ) = 0 := by simp [squaredMass]
@[simp] theorem spectralNorm_zero : spectralNorm (0 : ι → ℝ) = 0 := by simp [spectralNorm]

theorem spectralNorm_nonneg (u : ι → ℝ) : 0 ≤ spectralNorm u := Real.sqrt_nonneg _
theorem spectralNorm_pos {u : ι → ℝ} (hu : u ≠ 0) : 0 < spectralNorm u :=
  Real.sqrt_pos.mpr (squaredMass_pos hu)

theorem spectralNorm_eq_blockL2 (u : ι → ℝ) : spectralNorm u = BB.Blocks.blockL2 u := by
  simp only [spectralNorm,squaredMass,BB.Blocks.blockL2,Real.norm_eq_abs,sq_abs]

def simplexOfVector (u : ι → ℝ) (hu : u ≠ 0) : Simplex ι :=
  ⟨normalizedEnergy u,normalizedEnergy_nonneg u,normalizedEnergy_sum hu⟩

def normalizedVectorState (u v : ι → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) : NormalizedState ι :=
  (simplexOfVector v hv,simplexOfVector u hu)

def vectorOfSimplex (w : Simplex ι) : ι → ℝ := fun i => Real.sqrt (w.val i)

theorem squaredMass_vectorOfSimplex (w : Simplex ι) : squaredMass (vectorOfSimplex w) = 1 := by
  unfold squaredMass vectorOfSimplex
  simp only [Real.sq_sqrt (w.property.1 _)]
  exact w.property.2

theorem vectorOfSimplex_ne_zero (w : Simplex ι) : vectorOfSimplex w ≠ 0 := by
  intro hh
  have hmass := squaredMass_vectorOfSimplex w
  rw [hh,squaredMass_zero] at hmass
  norm_num at hmass

@[simp] theorem spectralNorm_vectorOfSimplex (w : Simplex ι) : spectralNorm (vectorOfSimplex w) = 1 := by
  rw [spectralNorm,squaredMass_vectorOfSimplex,Real.sqrt_one]

theorem simplexOfVector_vectorOfSimplex (w : Simplex ι) :
    simplexOfVector (vectorOfSimplex w) (vectorOfSimplex_ne_zero w) = w := by
  apply Subtype.ext
  funext i
  change (vectorOfSimplex w i)^2/squaredMass (vectorOfSimplex w) = w.val i
  rw [squaredMass_vectorOfSimplex,div_one,vectorOfSimplex,Real.sq_sqrt (w.property.1 i)]

/-- The reciprocal BB1 quotient is exactly the inverse normalized Rayleigh mean. -/
theorem vectorAlpha_normalized_tau (lam u : ι → ℝ) (hu : u ≠ 0) :
    vectorAlpha lam (fun _ => 1) u = 1/tau lam (simplexOfVector u hu).val := by
  have ht : tau lam (simplexOfVector u hu).val = quadraticForm lam u/squaredMass u := by
    unfold tau simplexOfVector normalizedEnergy quadraticForm
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [ht,one_div_div]
  simp only [vectorAlpha,quadraticForm,one_mul,squaredMass]

def bb1Step (lam u v : ι → ℝ) : ι → ℝ :=
  diagonalStep lam (vectorAlpha lam (fun _ => 1) u) v

theorem bb1Step_sq (lam u v : ι → ℝ) (hu : u ≠ 0) (i : ι) :
    bb1Step lam u v i^2 = simplexPhi lam (simplexOfVector u hu) i*(v i)^2 := by
  rw [bb1Step,diagonalStep,vectorAlpha_normalized_tau lam u hu,mul_pow]
  unfold simplexPhi
  congr 2
  ring

/-- The square of the radial factor is the exact squared physical norm ratio. -/
theorem squaredMass_bb1Step (lam u v : ι → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    squaredMass (bb1Step lam u v) =
      radialSquare lam (normalizedVectorState u v hu hv)*squaredMass v := by
  unfold squaredMass
  simp only [bb1Step_sq lam u v hu]
  change (∑ i, simplexPhi lam (simplexOfVector u hu) i*(v i)^2) =
    (∑ i, simplexPhi lam (simplexOfVector u hu) i*((v i)^2/squaredMass v))*squaredMass v
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hm := ne_of_gt (squaredMass_pos hv)
  field_simp

/-- The normalized multiplier is the genuine Euclidean gradient norm ratio. -/
theorem spectralNorm_bb1Step (lam u v : ι → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) :
    spectralNorm (bb1Step lam u v) =
      radialMultiplier lam (normalizedVectorState u v hu hv)*spectralNorm v := by
  unfold spectralNorm
  rw [squaredMass_bb1Step lam u v hu hv,
    Real.sqrt_mul (radialSquare_nonneg lam (normalizedVectorState u v hu hv))]
  rfl

theorem radialMultiplier_eq_zero_of_step_zero (lam u v : ι → ℝ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hstep : bb1Step lam u v = 0) :
    radialMultiplier lam (normalizedVectorState u v hu hv) = 0 := by
  have hh := spectralNorm_bb1Step lam u v hu hv
  rw [hstep,spectralNorm_zero] at hh
  exact (mul_eq_zero.mp hh.symm).resolve_right (ne_of_gt (spectralNorm_pos hv))

/-- Exact conjugacy between a nonterminal physical BB1 update and the simplex map. -/
theorem normalizedVectorState_step (lam u v : ι → ℝ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hstep : bb1Step lam u v ≠ 0) :
    normalizedMap lam (normalizedVectorState u v hu hv) =
      normalizedVectorState v (bb1Step lam u v) hv hstep := by
  have hmass := squaredMass_bb1Step lam u v hu hv
  have hm := squaredMass_pos hv
  have hpos : 0 < radialSquare lam (normalizedVectorState u v hu hv) := by
    have hh := squaredMass_pos hstep
    rw [hmass] at hh
    exact pos_of_mul_pos_left hh hm.le
  rw [normalizedMap_regular lam hpos]
  apply Prod.ext
  · apply Subtype.ext
    funext i
    change simplexPhi lam (simplexOfVector u hu) i*((v i)^2/squaredMass v)/
      radialSquare lam (normalizedVectorState u v hu hv) =
        (bb1Step lam u v i)^2/squaredMass (bb1Step lam u v)
    rw [bb1Step_sq lam u v hu,hmass]
    field_simp
    exact Or.inl (mul_comm _ _)
  · rfl

/-- Once a gradient vanishes, the current component remains zero under all later updates. -/
theorem iterate_current_zero (lam w u : ι → ℝ) (n : ℕ) :
    ((stateMap lam w)^[n] (u,0)).2 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change diagonalStep lam (vectorAlpha lam w (((stateMap lam w)^[n]) (u,0)).1)
      (((stateMap lam w)^[n]) (u,0)).2 = 0
    rw [ih]
    funext i
    simp [diagonalStep]

/-- The terminally extended multiplier equals the exact physical norm ratio for
every finite horizon, even when a gradient vanishes before that horizon. -/
theorem terminalMultiplier_physical (lam u v : ι → ℝ) (hu : u ≠ 0) (hv : v ≠ 0) (n : ℕ) :
    spectralNorm (((stateMap lam (fun _ => 1))^[n]) (u,v)).2 =
      terminalMultiplier (radialMultiplier lam) (normalizedMap lam) n
        (normalizedVectorState u v hu hv)*spectralNorm v := by
  induction n generalizing u v with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    change spectralNorm (((stateMap lam (fun _ => 1))^[n]) (v,bb1Step lam u v)).2 = _
    by_cases hstep : bb1Step lam u v = 0
    · rw [hstep,iterate_current_zero,spectralNorm_zero,terminalMultiplier_succ,
        radialMultiplier_eq_zero_of_step_zero lam u v hu hv hstep,zero_mul,zero_mul]
    · rw [ih v (bb1Step lam u v) hv hstep,terminalMultiplier_succ,
        normalizedVectorState_step lam u v hu hv hstep,spectralNorm_bb1Step lam u v hu hv]
      ring

end BB.Baseline
