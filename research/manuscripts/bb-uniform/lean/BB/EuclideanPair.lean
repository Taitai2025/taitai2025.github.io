import BB.OperatorFaceStep
import BB.SortedOperator
import Mathlib.Analysis.NormedSpace.ProdLp

/-! # The original Euclidean pair space and its actual spectral faces

`Pair E` carries the Hilbert product norm exactly, without norm-equivalence
loss.  All coordinates below are the actual orthogonal spectral projections.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean
open Module.End
open BB.Operator

abbrev Pair (E : Type*) := WithLp 2 (E × E)

def toPair {E : Type*} : Pair E → E × E := WithLp.equiv 2 (E × E)
def ofPair {E : Type*} : E × E → Pair E := (WithLp.equiv 2 (E × E)).symm

@[simp] theorem toPair_ofPair {E : Type*} (z : E × E) : toPair (ofPair z)=z := rfl
@[simp] theorem ofPair_toPair {E : Type*} (z : Pair E) : ofPair (toPair z)=z := rfl
@[simp] theorem toPair_fst {E : Type*} (z : Pair E) : (toPair z).1=z.fst := rfl
@[simp] theorem toPair_snd {E : Type*} (z : Pair E) : (toPair z).2=z.snd := rfl
@[simp] theorem ofPair_fst {E : Type*} (z : E × E) : (ofPair z).fst=z.1 := rfl
@[simp] theorem ofPair_snd {E : Type*} (z : E × E) : (ofPair z).snd=z.2 := rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

@[simp] theorem toPair_zero : toPair (0 : Pair E)=0 := rfl
@[simp] theorem ofPair_zero : ofPair (0 : E × E)=0 := rfl
@[simp] theorem toPair_sub (z y : Pair E) : toPair (z-y)=toPair z-toPair y := rfl
@[simp] theorem toPair_smul (t : ℝ) (z : Pair E) : toPair (t • z)=t • toPair z := rfl
@[simp] theorem ofPair_sub (z y : E × E) : ofPair (z-y)=ofPair z-ofPair y := rfl
@[simp] theorem ofPair_smul (t : ℝ) (z : E × E) : ofPair (t • z)=t • ofPair z := rfl

theorem norm_eq_pairNorm (z : Pair E) : ‖z‖=Operator.pairNorm (toPair z) :=
  WithLp.prod_norm_eq_of_L2 z

theorem norm_sq (z : Pair E) : ‖z‖^2=‖z.fst‖^2+‖z.snd‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 z

theorem norm_fst_le (z : Pair E) : ‖z.fst‖≤‖z‖ := by
  have h := norm_sq z
  nlinarith only [h,norm_nonneg z.fst,norm_nonneg z,sq_nonneg ‖z.snd‖]

theorem norm_snd_le (z : Pair E) : ‖z.snd‖≤‖z‖ := by
  have h := norm_sq z
  nlinarith only [h,norm_nonneg z.snd,norm_nonneg z,sq_nonneg ‖z.fst‖]

def cone (M : ℝ) (z : Pair E) : Prop := Operator.stateCone M (toPair z)

def T (H W : E →ₗ[ℝ] E) (z : Pair E) : Pair E := ofPair (Operator.stateMap H W (toPair z))

@[simp] theorem toPair_T (H W : E →ₗ[ℝ] E) (z : Pair E) :
    toPair (T H W z)=Operator.stateMap H W (toPair z) := rfl
@[simp] theorem T_zero (H W : E →ₗ[ℝ] E) : T H W 0=0 := by
  simp [T,Operator.stateMap_zero]

variable [FiniteDimensional ℝ E]

def supported {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (lo hi : Fin n) (u : E) : Prop :=
  ∀ i : Fin n, i<lo ∨ hi<i → Operator.sortedCoordinates hH hn u i=0

def stateSet {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (M : ℝ) (lo hi : Fin n) : Set (Pair E) :=
  {z | cone M z ∧ supported hH hn lo hi z.fst ∧ supported hH hn lo hi z.snd}

def P {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (lo hi : Fin n) (z : Pair E) : ℝ :=
  BB.geometricProduct (BB.endpointTheta (Operator.sortedLambda H hn lo) (Operator.sortedLambda H hn hi))
    ‖Operator.sortedCoordinates hH hn z.snd lo‖ ‖Operator.sortedCoordinates hH hn z.snd hi‖

def Q {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (lo hi : Fin n) (A : ℝ) (z : Pair E) : ℝ :=
  max ‖z‖ (A*P hH hn lo hi z)

theorem P_eq_actualEndpointProduct {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (lo hi : Fin n) (z : Pair E) :
    P hH hn lo hi z=Operator.actualEndpointProduct hH
      (Operator.spectralIndex H hn lo) (Operator.spectralIndex H hn hi) (toPair z) := rfl

end BB.Euclidean
