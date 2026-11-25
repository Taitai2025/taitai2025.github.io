import BB.OperatorBridge

set_option autoImplicit false

noncomputable section
namespace BB.Operator

open Module.End
open scoped BigOperators

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Increasing enumeration of the distinct eigenvalues, with a prescribed cardinal. -/
def spectralIndex (H : V →ₗ[ℝ] V) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n) :
    Fin n ≃o (Eigenvalues H) := monoEquivOfFin (Eigenvalues H) hn

def sortedLambda (H : V →ₗ[ℝ] V) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n) (i : Fin n) : ℝ :=
  (spectralIndex H hn i : ℝ)

abbrev SortedBlock (H : V →ₗ[ℝ] V) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n) (i : Fin n) :=
  ↥(eigenspace H (sortedLambda H hn i))

def sortedCoordinates {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (u : V) : ∀ i, SortedBlock H hn i :=
  fun i => coordinates hH u (spectralIndex H hn i)

def sortedStateCoordinates {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (z : V × V) : BB.Blocks.BState (SortedBlock H hn) :=
  (sortedCoordinates hH hn z.1,sortedCoordinates hH hn z.2)

/-- Strict monotonicity comes from sorting the actual distinct spectrum. -/
theorem sortedLambda_strictMono (H : V →ₗ[ℝ] V) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) : StrictMono (sortedLambda H hn) :=
  (spectralIndex H hn).strictMono

theorem sortedLambda_pos {H : V →ₗ[ℝ] V} {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n)
    (hpd : ∀ x : V, x ≠ 0 → 0 < @inner ℝ _ _ x (H x)) (i : Fin n) :
    0 < sortedLambda H hn i := eigenvalue_pos hpd (spectralIndex H hn i)

def sortedEnergy {H : V →ₗ[ℝ] V} {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n)
    (W : V →ₗ[ℝ] V) (i : Fin n) (x : SortedBlock H hn i) : ℝ := @inner ℝ _ _ (x:V) (W (x:V))

/-- Sorting only reindexes the exact weighted quotient. -/
theorem weightedAlpha_sorted {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n) (u : V) :
    weightedAlpha H W u = BB.Blocks.blockAlpha (sortedLambda H hn) (sortedEnergy hn W)
      (sortedCoordinates hH hn u) := by
  rw [weightedAlpha_blocks hH hcomm]
  unfold BB.Blocks.blockAlpha sortedLambda sortedEnergy sortedCoordinates coordinates blockEnergy
  congr 1
  · exact ((spectralIndex H hn).toEquiv.sum_comp
      (fun μ => @inner ℝ _ _ (hH.diagonalization u μ : V) (W (hH.diagonalization u μ : V)))).symm
  · exact ((spectralIndex H hn).toEquiv.sum_comp
      (fun μ => (μ:ℝ)*@inner ℝ _ _ (hH.diagonalization u μ : V) (W (hH.diagonalization u μ : V)))).symm

/-- Exact sorted-coordinate conjugacy for the original operator iteration. -/
theorem sortedStateMap_conjugacy {H W : V →ₗ[ℝ] V} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n) (z : V × V) :
    sortedStateCoordinates hH hn (stateMap H W z) =
      BB.Blocks.blockMap (sortedLambda H hn) (sortedEnergy hn W) (sortedStateCoordinates hH hn z) := by
  apply Prod.ext
  · rfl
  · funext i
    change hH.diagonalization (z.2-weightedAlpha H W z.1 • H z.2) (spectralIndex H hn i) =
      (1-BB.Blocks.blockAlpha (sortedLambda H hn) (sortedEnergy hn W) (sortedCoordinates hH hn z.1)*
        sortedLambda H hn i) • hH.diagonalization z.2 (spectralIndex H hn i)
    rw [map_sub,map_smul]
    change hH.diagonalization z.2 (spectralIndex H hn i) -
      weightedAlpha H W z.1 • hH.diagonalization (H z.2) (spectralIndex H hn i) = _
    rw [hH.diagonalization_apply_self_apply,weightedAlpha_sorted hH hcomm hn]
    rw [smul_smul,sub_smul,one_smul]
    rfl

theorem sortedCoordinates_sq_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (u : V) :
    (∑ i, ‖sortedCoordinates hH hn u i‖^2) = ‖u‖^2 := by
  unfold sortedCoordinates
  exact ((spectralIndex H hn).toEquiv.sum_comp (fun μ => ‖coordinates hH u μ‖^2)).trans
    (coordinates_sq_norm hH u)

theorem sortedCoordinates_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (u : V) :
    BB.Blocks.blockL2 (sortedCoordinates hH hn u) = ‖u‖ := by
  unfold BB.Blocks.blockL2
  rw [sortedCoordinates_sq_norm,Real.sqrt_sq (norm_nonneg _)]

theorem sortedStateCoordinates_norm {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (z : V × V) :
    BB.Blocks.stateL2 (sortedStateCoordinates hH hn z) = Real.sqrt (‖z.1‖^2+‖z.2‖^2) := by
  unfold BB.Blocks.stateL2 sortedStateCoordinates
  rw [sortedCoordinates_sq_norm,sortedCoordinates_sq_norm]

theorem sortedCoordinates_sub {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (u v : V) :
    sortedCoordinates hH hn (u-v) = sortedCoordinates hH hn u-sortedCoordinates hH hn v := by
  funext i
  exact congrArg (fun x => x (spectralIndex H hn i)) (hH.diagonalization.map_sub u v)

theorem sortedStateCoordinates_sub {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (z z' : V × V) :
    sortedStateCoordinates hH hn (z-z') = sortedStateCoordinates hH hn z-sortedStateCoordinates hH hn z' :=
  Prod.ext (sortedCoordinates_sub hH hn _ _) (sortedCoordinates_sub hH hn _ _)

theorem sortedCoordinates_smul {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (t : ℝ) (u : V) :
    sortedCoordinates hH hn (t • u) = t • sortedCoordinates hH hn u := by
  funext i
  exact congrArg (fun x => x (spectralIndex H hn i)) (hH.diagonalization.map_smul t u)

theorem sortedStateCoordinates_smul {H : V →ₗ[ℝ] V} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) (t : ℝ) (z : V × V) :
    sortedStateCoordinates hH hn (t • z) = t • sortedStateCoordinates hH hn z :=
  Prod.ext (sortedCoordinates_smul hH hn _ _) (sortedCoordinates_smul hH hn _ _)

/-- All block energy bounds are inherited from the original operator. -/
theorem sortedEnergy_bounds {H W : V →ₗ[ℝ] V} {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n)
    {m χ : ℝ} (hlo : ∀ x : V, m*‖x‖^2 ≤ @inner ℝ _ _ x (W x))
    (hhi : ∀ x : V, @inner ℝ _ _ x (W x) ≤ (χ*m)*‖x‖^2) :
    (∀ i (x : SortedBlock H hn i), m*‖x‖^2 ≤ sortedEnergy hn W i x) ∧
    (∀ i (x : SortedBlock H hn i), sortedEnergy hn W i x ≤ (χ*m)*‖x‖^2) := by
  exact ⟨fun i x => hlo (x:V),fun i x => hhi (x:V)⟩

end BB.Operator
