import BB.DiagonalTheorem
import BB.BlockEnergy

/-!
# Uniform Euclidean theorem on arbitrary spectral blocks

The scalar certificate and the constants below are chosen before the block
spaces or the weight family are supplied.  Thus their displayed definitions
make independence from eigenspace multiplicities explicit.
-/

noncomputable section
namespace BB.Blocks

open BB.Spectral BB.Gluing BB.Diagonal
open scoped BigOperators

variable {n : ℕ}

def enlargedCone (lam : Fin (n+2) → ℝ) (M : ℝ) : ℝ :=
  max (M * Real.sqrt (n+2 : ℕ)) (max 1 (lam (Fin.last (n+1))/lam 0 - 1))

theorem enlargedCone_one (lam : Fin (n+2) → ℝ) (M : ℝ) : 1 ≤ enlargedCone lam M :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem enlargedCone_step (lam : Fin (n+2) → ℝ) (M : ℝ) :
    lam (Fin.last (n+1))/lam 0 - 1 ≤ enlargedCone lam M :=
  (le_max_right _ _).trans (le_max_right _ _)

def scalarCertificate (lam : Fin (n+2) → ℝ) {χ : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (M : ℝ) :
    Certificate (T lam (χ := χ)) {z | Cone (enlargedCone lam M) z}
      (BB.endpointRate (lam 0) (lam (Fin.last (n+1)))) :=
  Classical.choose (full_exact_rate lam hmono ha hχ (enlargedCone_one lam M) (enlargedCone_step lam M))

theorem scalarCertificate_abs (lam : Fin (n+2) → ℝ) {χ : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (M : ℝ)
    (z : State (Fin (n+2))) :
    (scalarCertificate lam hmono ha hχ M).value (absState z) =
      (scalarCertificate lam hmono ha hχ M).value z :=
  Classical.choose_spec (full_exact_rate lam hmono ha hχ
    (enlargedCone_one lam M) (enlargedCone_step lam M)) z

def euclideanFactor (n : ℕ) : ℝ := Real.sqrt (2 * (n+2 : ℕ))

theorem euclideanFactor_nonneg (n : ℕ) : 0 ≤ euclideanFactor n := Real.sqrt_nonneg _

theorem euclideanFactor_ge_one (n : ℕ) : 1 ≤ euclideanFactor n := by
  unfold euclideanFactor
  apply (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by positivity)).mpr
  norm_num
  nlinarith [show (0 : ℝ) ≤ (n : ℝ) by positivity]

/-- This prefactor has no block-space or weight-family argument. -/
def uniformPrefactor (lam : Fin (n+2) → ℝ) {χ : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (M : ℝ) : ℝ :=
  euclideanFactor n * (scalarCertificate lam hmono ha hχ M).prefactor

variable {E : Fin (n+2) → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

theorem l2Cone_into_enlarged {lam : Fin (n+2) → ℝ} {M : ℝ}
    (hM : 0 ≤ M) {z : BState E} (hz : l2Cone M z) : blockCone (enlargedCone lam M) z := by
  have h := l2Cone_implies_blockCone hM hz
  simp only [Fintype.card_fin] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg z.1))

/-- A common Lyapunov function measured in the manuscript's Euclidean pair norm. -/
structure L2Certificate {Ω : Type*} (F : Ω → BState E → BState E) (M c K : ℝ) where
  value : BState E → ℝ
  lipConstant : ℝ
  prefactor_ge_one : 1 ≤ K
  lipConstant_nonneg : 0 ≤ lipConstant
  lower : ∀ z : BState E, l2Cone M z → stateL2 z ≤ value z
  upper : ∀ z : BState E, l2Cone M z → value z ≤ K * stateL2 z
  lipschitz : ∀ x y : BState E, l2Cone M x → l2Cone M y →
    |value x - value y| ≤ lipConstant * stateL2 (x-y)
  homogeneous : ∀ z : BState E, l2Cone M z → ∀ t : ℝ, 0 ≤ t → value (t • z) = t * value z
  decrease : ∀ (ω : Ω) (z : BState E), l2Cone M z → value (F ω z) ≤ c * value z

/-- The complete spectral-block theorem, with arbitrary positive scales for
the changing weights and no restriction on block dimensions. -/
theorem uniform_block_certificate {Ω : Type*}
    (lam : Fin (n+2) → ℝ) {χ M : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (hM : 0 ≤ M)
    (q : Ω → ∀ i, E i → ℝ) (m : Ω → ℝ) (hm : ∀ ω, 0 < m ω)
    (hqlo : ∀ ω i x, m ω*‖x‖^2 ≤ q ω i x)
    (hqhi : ∀ ω i x, q ω i x ≤ (χ*m ω)*‖x‖^2) :
    Nonempty (L2Certificate (fun ω => blockMap lam (q ω)) M
      (BB.endpointRate (lam 0) (lam (Fin.last (n+1))))
      (uniformPrefactor lam hmono ha hχ M)) := by
  let q' : Ω → ∀ i, E i → ℝ := fun ω i x => q ω i x / m ω
  have hlo : ∀ ω i x, ‖x‖^2 ≤ q' ω i x :=
    fun ω => (normalized_energy_bounds (hm ω) (hqlo ω) (hqhi ω)).1
  have hhi : ∀ ω i x, q' ω i x ≤ χ*‖x‖^2 :=
    fun ω => (normalized_energy_bounds (hm ω) (hqlo ω) (hqhi ω)).2
  let v := scalarCertificate lam hmono ha hχ M
  let vb := liftCertificate q' hχ hlo hhi v (scalarCertificate_abs lam hmono ha hχ M)
  let F := euclideanFactor n
  have hF : 0 ≤ F := euclideanFactor_nonneg n
  have hF1 : 1 ≤ F := euclideanFactor_ge_one n
  have hvK : 1 ≤ vb.prefactor := v.prefactor_ge_one
  have hnorm (z : BState E) : stateL2 z ≤ F * ‖z‖ := by
    simpa only [Fintype.card_fin] using stateL2_le z
  have hcone : ∀ z : BState E, l2Cone M z → blockCone (enlargedCone lam M) z :=
    fun z hz => l2Cone_into_enlarged (lam := lam) hM hz
  refine ⟨{
    value := fun z => F * vb.value z
    lipConstant := F * vb.lipConstant
    prefactor_ge_one := ?_
    lipConstant_nonneg := mul_nonneg hF vb.lipConstant_nonneg
    lower := ?_
    upper := ?_
    lipschitz := ?_
    homogeneous := ?_
    decrease := ?_
  }⟩
  · change 1 ≤ F * vb.prefactor
    nlinarith
  · intro z hz
    exact (hnorm z).trans (mul_le_mul_of_nonneg_left (vb.lower z (hcone z hz)) hF)
  · intro z hz
    change F * vb.value z ≤ (F * vb.prefactor) * stateL2 z
    have h := mul_le_mul_of_nonneg_left (vb.upper z (hcone z hz)) hF
    have h' := mul_le_mul_of_nonneg_left (norm_le_stateL2 z)
      (mul_nonneg hF (by linarith : 0 ≤ vb.prefactor))
    nlinarith only [h,h']
  · intro x y hx hy
    rw [← mul_sub, abs_mul, abs_of_nonneg hF]
    have h := mul_le_mul_of_nonneg_left (vb.lipschitz x y (hcone x hx) (hcone y hy)) hF
    have h' := mul_le_mul_of_nonneg_left (norm_le_stateL2 (x-y))
      (mul_nonneg hF vb.lipConstant_nonneg)
    nlinarith only [h,h']
  · intro z hz t ht
    change F * vb.value (t • z) = t * (F * vb.value z)
    rw [vb.homogeneous z (hcone z hz) t ht]
    ring
  · intro ω z hz
    change F * vb.value (blockMap lam (q ω) z) ≤
      BB.endpointRate (lam 0) (lam (Fin.last (n+1))) * (F * vb.value z)
    have heq : blockMap lam (q' ω) z = blockMap lam (q ω) z :=
      blockMap_scale lam (q ω) z (hm ω).ne'
    rw [← heq]
    have h := mul_le_mul_of_nonneg_left (vb.decrease ω z (hcone z hz)) hF
    nlinarith only [h]

/-- Uniform exact-rate estimate for all block trajectories; only the initial
pair is required to belong to the original Euclidean cone. -/
theorem uniform_block_rate {Ω : Type*}
    (lam : Fin (n+2) → ℝ) {χ M : ℝ}
    (hmono : StrictMono lam) (ha : 0 < lam 0) (hχ : 1 ≤ χ) (hM : 0 ≤ M)
    (q : Ω → ∀ i, E i → ℝ) (m : Ω → ℝ) (hm : ∀ ω, 0 < m ω)
    (hqlo : ∀ ω i x, m ω*‖x‖^2 ≤ q ω i x)
    (hqhi : ∀ ω i x, q ω i x ≤ (χ*m ω)*‖x‖^2)
    (w : ℕ → Ω) (z : ℕ → BState E) (hz : l2Cone M (z 0))
    (hrec : ∀ k, z (k+1) = blockMap lam (q (w k)) (z k)) (k : ℕ) :
    stateL2 (z k) ≤ uniformPrefactor lam hmono ha hχ M *
      (BB.endpointRate (lam 0) (lam (Fin.last (n+1))))^k * stateL2 (z 0) := by
  let q' : Ω → ∀ i, E i → ℝ := fun ω i x => q ω i x / m ω
  have hlo : ∀ ω i x, ‖x‖^2 ≤ q' ω i x :=
    fun ω => (normalized_energy_bounds (hm ω) (hqlo ω) (hqhi ω)).1
  have hhi : ∀ ω i x, q' ω i x ≤ χ*‖x‖^2 :=
    fun ω => (normalized_energy_bounds (hm ω) (hqlo ω) (hqhi ω)).2
  let v := scalarCertificate lam hmono ha hχ M
  let vb := liftCertificate q' hχ hlo hhi v (scalarCertificate_abs lam hmono ha hχ M)
  have hrec' : ∀ j, z (j+1) = blockMap lam (q' (w j)) (z j) := by
    intro j
    rw [hrec j]
    exact (blockMap_scale lam (q (w j)) (z j) (hm (w j)).ne').symm
  have hstates : ∀ j, blockCone (enlargedCone lam M) (z j) := by
    intro j
    induction j with
    | zero => exact l2Cone_into_enlarged hM hz
    | succ j ih =>
      rw [hrec' j]
      exact blockMap_cone ha (hmono.monotone (Fin.zero_le _)) hχ
        (fun i => hmono.monotone (Fin.zero_le i)) (fun i => hmono.monotone (Fin.le_last i))
        (enlargedCone_step lam M) (hlo (w j)) (hhi (w j)) ih
  have hc : 0 ≤ BB.endpointRate (lam 0) (lam (Fin.last (n+1))) := by
    apply (BB.endpointRate_pos ha (hmono ?_)).le
    change 0 < n+1
    omega
  have hb := vb.trajectory_bound hc z w hstates hrec' k
  have hK : 0 ≤ vb.prefactor := (by norm_num : (0:ℝ) ≤ 1).trans vb.prefactor_ge_one
  have h := l2_rate_from_sup hK (pow_nonneg hc k) hb
  simpa only [Fintype.card_fin] using h

end BB.Blocks
