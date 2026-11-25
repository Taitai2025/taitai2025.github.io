import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Data.Fintype.Sort
import BB.BlockEnergy

set_option autoImplicit false

/-!
# The actual self-adjoint operator to spectral-block bridge

The decomposition is mathlib's proved finite-dimensional spectral theorem.
The eigenspace index counts distinct eigenvalues, not eigenvectors.
-/

noncomputable section
namespace BB.Operator

open Module.End
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Commutation preserves each actual eigenspace. -/
theorem commute_preserves_eigenspace {H W : V →ₗ[ℝ] V}
    (hcomm : Function.Commute H W) {μ : ℝ} {x : V} (hx : x ∈ eigenspace H μ) :
    W x ∈ eigenspace H μ := by
  apply mem_eigenspace_iff.mpr
  rw [hcomm x,mem_eigenspace_iff.mp hx,W.map_smul]

/-- Restriction of a commuting operator to one eigenspace. -/
def eigenAction {H W : V →ₗ[ℝ] V} (hcomm : Function.Commute H W) (μ : (Eigenvalues H)) :
    eigenspace H (μ:ℝ) →ₗ[ℝ] eigenspace H (μ:ℝ) where
  toFun x := ⟨W x,commute_preserves_eigenspace hcomm x.property⟩
  map_add' x y := by apply Subtype.ext; exact W.map_add _ _
  map_smul' t x := by apply Subtype.ext; exact W.map_smul t x

variable [FiniteDimensional ℝ V]

/-- The real order inherited by the finite subtype of distinct eigenvalues. -/
instance eigenvaluesLinearOrder (H : V →ₗ[ℝ] V) : LinearOrder (Eigenvalues H) :=
  inferInstanceAs (LinearOrder {μ : ℝ // HasEigenvalue H μ})

/-- Block coordinates supplied by the standard self-adjoint spectral theorem. -/
def coordinates {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) (u : V) :
    ∀ μ : (Eigenvalues H), eigenspace H (μ:ℝ) := fun μ => hH.diagonalization u μ

/-- The isometry gives exact Euclidean block norm equality. -/
theorem coordinates_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) (u : V) :
    BB.Blocks.blockL2 (coordinates hH u) = ‖u‖ := by
  change Real.sqrt (∑ μ, ‖hH.diagonalization u μ‖^2) = ‖u‖
  rw [← PiLp.norm_eq_of_L2,hH.diagonalization.norm_map]

/-- Squared-norm form of Parseval for the eigenspace decomposition. -/
theorem coordinates_sq_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) (u : V) :
    (∑ μ, ‖coordinates hH u μ‖^2) = ‖u‖^2 := by
  rw [← BB.Blocks.blockL2_sq,coordinates_norm]

/-- A commuting operator acts separately on the spectral blocks. -/
theorem diagonalization_commuting {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) (u : V) (μ : (Eigenvalues H)) :
    hH.diagonalization (W u) μ = eigenAction hcomm μ (hH.diagonalization u μ) := by
  let y : PiLp 2 (fun ν : (Eigenvalues H) => eigenspace H (ν:ℝ)) :=
    fun ν => eigenAction hcomm ν (hH.diagonalization u ν)
  have hrec : (∑ ν : (Eigenvalues H), (hH.diagonalization u ν : V)) = u := by
    rw [← hH.diagonalization_symm_apply,hH.diagonalization.symm_apply_apply]
  have hy : hH.diagonalization.symm y = W u := by
    rw [hH.diagonalization_symm_apply]
    change (∑ ν : (Eigenvalues H), W (hH.diagonalization u ν)) = W u
    rw [← map_sum,hrec]
  have hh := congrArg (fun x => hH.diagonalization x μ) hy
  dsimp only at hh
  rw [hH.diagonalization.apply_symm_apply] at hh
  exact hh.symm

/-- Weighted mixed inner products split into their actual eigenspace components. -/
theorem mixed_inner_decomposition {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) (u v : V) :
    @inner ℝ _ _ u (W v) =
      ∑ μ : (Eigenvalues H), @inner ℝ _ _ (coordinates hH u μ : V) (W (coordinates hH v μ : V)) := by
  calc
    @inner ℝ _ _ u (W v) = @inner ℝ _ _ (hH.diagonalization u) (hH.diagonalization (W v)) :=
      (hH.diagonalization.inner_map_map _ _).symm
    _ = ∑ μ : (Eigenvalues H), @inner ℝ _ _ (hH.diagonalization u μ) (hH.diagonalization (W v) μ) :=
      PiLp.inner_apply _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro μ _
      rw [diagonalization_commuting hH hcomm]
      rfl

/-- Weighted Hessian moments split with the corresponding eigenvalue factor. -/
theorem moment_inner_decomposition {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) (u : V) :
    @inner ℝ _ _ u (W (H u)) =
      ∑ μ : (Eigenvalues H), (μ:ℝ) * @inner ℝ _ _ (coordinates hH u μ : V) (W (coordinates hH u μ : V)) := by
  rw [mixed_inner_decomposition hH hcomm]
  apply Finset.sum_congr rfl
  intro μ _
  unfold coordinates
  rw [hH.diagonalization_apply_self_apply]
  change @inner ℝ _ _ (hH.diagonalization u μ : V) (W ((μ:ℝ) • (hH.diagonalization u μ : V))) = _
  rw [W.map_smul,inner_smul_right]

def weightedAlpha (H W : V →ₗ[ℝ] V) (u : V) : ℝ :=
  @inner ℝ _ _ u (W u) / @inner ℝ _ _ u (W (H u))

def blockEnergy {H : V →ₗ[ℝ] V} (W : V →ₗ[ℝ] V) (μ : (Eigenvalues H))
    (x : eigenspace H (μ:ℝ)) : ℝ := @inner ℝ _ _ (x:V) (W (x:V))

/-- The original weighted Rayleigh stepsize equals the actual block quotient. -/
theorem weightedAlpha_blocks {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) (u : V) :
    weightedAlpha H W u =
      BB.Blocks.blockAlpha (fun μ : (Eigenvalues H) => (μ:ℝ)) (blockEnergy W) (coordinates hH u) := by
  unfold weightedAlpha BB.Blocks.blockAlpha blockEnergy
  rw [mixed_inner_decomposition hH hcomm,moment_inner_decomposition hH hcomm]

/-- The actual quadratic-gradient state update. -/
def stateMap (H W : V →ₗ[ℝ] V) (z : V × V) : V × V :=
  (z.2,z.2-weightedAlpha H W z.1 • H z.2)

def stateCoordinates {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) (z : V × V) :
    BB.Blocks.BState (fun μ : (Eigenvalues H) => eigenspace H (μ:ℝ)) :=
  (coordinates hH z.1,coordinates hH z.2)

/-- Exact conjugacy of the operator update and the spectral-block update. -/
theorem stateMap_conjugacy {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) (z : V × V) :
    stateCoordinates hH (stateMap H W z) =
      BB.Blocks.blockMap (fun μ : (Eigenvalues H) => (μ:ℝ)) (blockEnergy W) (stateCoordinates hH z) := by
  apply Prod.ext
  · rfl
  · funext μ
    change hH.diagonalization (z.2-weightedAlpha H W z.1 • H z.2) μ =
      (1-BB.Blocks.blockAlpha (fun μ : (Eigenvalues H) => (μ:ℝ)) (blockEnergy W) (coordinates hH z.1)*(μ:ℝ)) •
        hH.diagonalization z.2 μ
    rw [map_sub,map_smul]
    change hH.diagonalization z.2 μ - weightedAlpha H W z.1 • hH.diagonalization (H z.2) μ = _
    rw [hH.diagonalization_apply_self_apply,weightedAlpha_blocks hH hcomm]
    rw [smul_smul,sub_smul,one_smul]

/-- Exact Euclidean pair norm equality across the spectral transform. -/
theorem stateCoordinates_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) (z : V × V) :
    BB.Blocks.stateL2 (stateCoordinates hH z) = Real.sqrt (‖z.1‖^2+‖z.2‖^2) := by
  unfold BB.Blocks.stateL2 stateCoordinates
  rw [coordinates_sq_norm,coordinates_sq_norm]

/-- Actual operator quadratic-form bounds transfer unchanged to every block. -/
theorem blockEnergy_bounds {H W : V →ₗ[ℝ] V} {m χ : ℝ}
    (hlo : ∀ x : V, m*‖x‖^2 ≤ @inner ℝ _ _ x (W x))
    (hhi : ∀ x : V, @inner ℝ _ _ x (W x) ≤ (χ*m)*‖x‖^2) :
    (∀ (μ : Eigenvalues H) (x : eigenspace H (μ:ℝ)), m*‖x‖^2 ≤ blockEnergy W μ x) ∧
    (∀ (μ : Eigenvalues H) (x : eigenspace H (μ:ℝ)), blockEnergy W μ x ≤ (χ*m)*‖x‖^2) := by
  constructor
  · intro μ x; exact hlo (x:V)
  · intro μ x; exact hhi (x:V)

/-- Positive definiteness implies positivity of each distinct eigenvalue. -/
theorem eigenvalue_pos {H : V →ₗ[ℝ] V}
    (hpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (H x)) (μ : (Eigenvalues H)) : 0 < (μ:ℝ) := by
  obtain ⟨x,hx⟩ := μ.property.exists_hasEigenvector
  have hp := hpd x hx.2
  rw [hx.apply_eq_smul,inner_smul_right,real_inner_self_eq_norm_sq] at hp
  exact pos_of_mul_pos_left hp (sq_nonneg _)

end BB.Operator
