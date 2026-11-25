import BB.NormalizedOrbit
import BB.BlockTheorem
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section
namespace BB.Baseline
open scoped BigOperators Topology
open BB.Spectral Filter

variable {n : ℕ}

theorem scalar_blockMap_eq_bb1 (lam : Fin (n+2) → ℝ) (z : State (Fin (n+2))) :
    BB.Blocks.blockMap lam (fun _ (x : ℝ) => x^2) z = stateMap lam (fun _ => 1) z := by
  ext i <;> simp only [BB.Blocks.blockMap,BB.Blocks.blockAlpha,stateMap,diagonalStep,
    vectorAlpha,quadraticForm,one_mul,smul_eq_mul]

/-- The exact quadratic theorem gives a uniform critical-rate bound for every
terminally extended normalized multiplier, with no matching requirement on the
two independently prescribed simplex components. -/
theorem normalized_multiplier_uniform_bound (lam : Fin (n+2) → ℝ)
    (hmono : StrictMono lam) (ha : 0 < lam 0) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ k : ℕ, ∀ chi : NormalizedState (Fin (n+2)),
      terminalMultiplier (radialMultiplier lam) (normalizedMap lam) k chi ≤
        K*(BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^k := by
  let C := BB.Blocks.uniformPrefactor lam hmono ha (show (1 : ℝ) ≤ 1 by rfl) 1
  let K := max 1 (C*Real.sqrt 2)
  refine ⟨K,le_max_left _ _,?_⟩
  intro k chi
  let u := vectorOfSimplex chi.2
  let v := vectorOfSimplex chi.1
  let z : ℕ → State (Fin (n+2)) := fun j => ((stateMap lam (fun _ => 1))^[j]) (u,v)
  have hu : u ≠ 0 := vectorOfSimplex_ne_zero chi.2
  have hv : v ≠ 0 := vectorOfSimplex_ne_zero chi.1
  have hz : BB.Blocks.l2Cone 1 (z 0) := by
    change BB.Blocks.blockL2 v ≤ 1*BB.Blocks.blockL2 u
    rw [← spectralNorm_eq_blockL2,← spectralNorm_eq_blockL2]
    change spectralNorm (vectorOfSimplex chi.1) ≤ 1*spectralNorm (vectorOfSimplex chi.2)
    simp
  have hrec : ∀ j, z (j+1) = BB.Blocks.blockMap lam (fun _ (x : ℝ) => x^2) (z j) := by
    intro j
    rw [scalar_blockMap_eq_bb1]
    exact Function.iterate_succ_apply' _ _ _
  have hb := BB.Blocks.uniform_block_rate (E := fun _ : Fin (n+2) => ℝ)
    lam hmono ha (show (1 : ℝ) ≤ 1 by rfl) (show (0 : ℝ) ≤ 1 by norm_num)
    (fun (_ : Unit) _ (x : ℝ) => x^2) (fun _ => 1) (fun _ => by norm_num)
    (fun _ _ x => by simp only [one_mul,Real.norm_eq_abs,sq_abs]; exact le_refl _)
    (fun _ _ x => by simp only [one_mul,Real.norm_eq_abs,sq_abs]; exact le_refl _)
    (fun _ => ()) z hz hrec k
  have hstart : BB.Blocks.stateL2 (z 0) = Real.sqrt 2 := by
    change Real.sqrt ((∑ i, ‖u i‖^2)+(∑ i, ‖v i‖^2)) = Real.sqrt 2
    simp only [Real.norm_eq_abs,sq_abs]
    change Real.sqrt (squaredMass (vectorOfSimplex chi.2)+squaredMass (vectorOfSimplex chi.1)) = _
    rw [squaredMass_vectorOfSimplex,squaredMass_vectorOfSimplex]
    norm_num
  have hphysical : spectralNorm (z k).2 =
      terminalMultiplier (radialMultiplier lam) (normalizedMap lam) k chi := by
    have hh := terminalMultiplier_physical lam (vectorOfSimplex chi.2) (vectorOfSimplex chi.1)
      (vectorOfSimplex_ne_zero chi.2) (vectorOfSimplex_ne_zero chi.1) k
    simpa only [normalizedVectorState,simplexOfVector_vectorOfSimplex,
      spectralNorm_vectorOfSimplex,mul_one] using hh
  have hcurrent : spectralNorm (z k).2 ≤ BB.Blocks.stateL2 (z k) := by
    rw [spectralNorm_eq_blockL2]
    apply Real.sqrt_le_sqrt
    exact le_add_of_nonneg_left (Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hc : 0 ≤ BB.endpointRate (lam 0) (lam (Fin.last (n+1))) := by
    apply (BB.endpointRate_pos ha (hmono ?_)).le
    change 0 < n+1
    omega
  rw [hstart] at hb
  calc
    terminalMultiplier (radialMultiplier lam) (normalizedMap lam) k chi ≤ BB.Blocks.stateL2 (z k) := by
      rw [← hphysical]
      exact hcurrent
    _ ≤ C*(BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^k*Real.sqrt 2 := hb
    _ = (C*Real.sqrt 2)*(BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^k := by ring
    _ ≤ K*(BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^k :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hc k)

/-- The original normalized block-contraction conclusion follows with one fixed
horizon for all states, which is stronger than a state-dependent horizon. -/
theorem normalized_block_contraction (lam : Fin (n+2) → ℝ)
    (hmono : StrictMono lam) (ha : 0 < lam 0) :
    ∃ L : ℕ, 1 ≤ L ∧ ∀ chi : NormalizedState (Fin (n+2)),
      terminalMultiplier (radialMultiplier lam) (normalizedMap lam) L chi ≤ 1/2 := by
  obtain ⟨K,hK,hbound⟩ := normalized_multiplier_uniform_bound lam hmono ha
  have hab : lam 0 < lam (Fin.last (n+1)) := hmono (by change 0 < n+1; omega)
  have hcpos := BB.endpointRate_pos ha hab
  have hcone := BB.endpointRate_lt_one ha hab
  have hlimit : Tendsto
      (fun j : ℕ => K*(BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^j) atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one hcpos.le hcone).const_mul K
    simpa only [mul_zero] using hh
  have hevent : ∀ᶠ j : ℕ in atTop, K*(BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^j < 1/2 :=
    hlimit.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  obtain ⟨L,hL,hgood⟩ := ((eventually_ge_atTop 1).and hevent).exists
  exact ⟨L,hL,fun chi => (hbound L chi).trans hgood.le⟩

/-- The precise existential form of the baseline proposition, with `q=1/2`. -/
theorem baseline_block_contraction (lam : Fin (n+2) → ℝ)
    (hmono : StrictMono lam) (ha : 0 < lam 0) :
    ∃ L : ℕ, ∃ q : ℝ, 1 ≤ L ∧ 0 < q ∧ q < 1 ∧
      ∀ chi : NormalizedState (Fin (n+2)), ∃ ell : ℕ,
        1 ≤ ell ∧ ell ≤ L ∧
          terminalMultiplier (radialMultiplier lam) (normalizedMap lam) ell chi ≤ q := by
  obtain ⟨L,hL,hbound⟩ := normalized_block_contraction lam hmono ha
  exact ⟨L,1/2,hL,by norm_num,by norm_num,fun chi => ⟨L,hL,le_refl L,hbound chi⟩⟩

/-- The one-eigenvalue simplex is terminal after its first update. -/
theorem normalized_singleton_terminal (lam : Fin 1 → ℝ) (ha : 0 < lam 0)
    (chi : NormalizedState (Fin 1)) : radialMultiplier lam chi = 0 := by
  have hw : chi.1.val 0 = 1 := by simpa only [Fin.sum_univ_one] using chi.1.property.2
  have hz : chi.2.val 0 = 1 := by simpa only [Fin.sum_univ_one] using chi.2.property.2
  simp only [radialMultiplier,radialSquare,simplexPhi,tau,Fin.sum_univ_one,hw,hz,mul_one,
    div_self (ne_of_gt ha),sub_self,zero_pow (by decide : 2 ≠ 0),Real.sqrt_zero]

end BB.Baseline
