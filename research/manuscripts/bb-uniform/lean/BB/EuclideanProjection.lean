import BB.SortedOperator
import BB.EndpointPersistence

/-! # Orthogonal spectral deletion in the original Euclidean space -/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean
open Module.End
open BB.Operator
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

 theorem coordinate_norm_le {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) (i : Fin n) :
    ‖sortedCoordinates hH hn u i‖≤‖u‖ := by
  have hs : ‖sortedCoordinates hH hn u i‖^2 ≤
      ∑ j : Fin n, ‖sortedCoordinates hH hn u j‖^2 :=
    Finset.single_le_sum (f := fun j : Fin n => ‖sortedCoordinates hH hn u j‖^2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  rw [sortedCoordinates_sq_norm] at hs
  nlinarith only [hs,norm_nonneg (sortedCoordinates hH hn u i),norm_nonneg u]

 theorem sortedCoordinates_injective {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) : Function.Injective (sortedCoordinates hH hn) := by
  intro u v huv
  apply hH.diagonalization.injective
  apply PiLp.ext
  intro mu
  obtain ⟨i,rfl⟩ := (spectralIndex H hn).surjective mu
  exact congrFun huv i

/-- Erase one actual orthogonal eigenspace component and reconstruct the vector. -/
def erase {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) (i : Fin n) : E :=
  hH.diagonalization.symm (fun mu => if mu=spectralIndex H hn i then 0 else coordinates hH u mu)

 theorem sortedCoordinates_erase {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) (i j : Fin n) :
    sortedCoordinates hH hn (erase hH hn u i) j =
      if j=i then 0 else sortedCoordinates hH hn u j := by
  change (hH.diagonalization (hH.diagonalization.symm _)) (spectralIndex H hn j) = _
  rw [hH.diagonalization.apply_symm_apply]
  simp only [EquivLike.apply_eq_iff_eq]
  rfl

@[simp] theorem erase_self {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) (i : Fin n) :
    sortedCoordinates hH hn (erase hH hn u i) i=0 := by
  simp [sortedCoordinates_erase]

 theorem erase_other {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) {i j : Fin n} (hji : j≠i) :
    sortedCoordinates hH hn (erase hH hn u i) j=sortedCoordinates hH hn u j := by
  simp only [sortedCoordinates_erase,if_neg hji]

 theorem erase_norm_le {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) (i : Fin n) :
    ‖erase hH hn u i‖≤‖u‖ := by
  have hs : ‖erase hH hn u i‖^2≤‖u‖^2 := by
    rw [← sortedCoordinates_sq_norm hH hn,← sortedCoordinates_sq_norm hH hn]
    apply Finset.sum_le_sum
    intro j _
    by_cases hji : j=i
    · subst j
      simp only [erase_self,norm_zero,zero_pow (by decide : 2≠0)]
      exact sq_nonneg _
    · rw [erase_other hH hn u hji]
  nlinarith only [hs,norm_nonneg (erase hH hn u i),norm_nonneg u]

 theorem norm_sub_erase {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H)=n) (u : E) (i : Fin n) :
    ‖u-erase hH hn u i‖=‖sortedCoordinates hH hn u i‖ := by
  have hs : ‖u-erase hH hn u i‖^2=‖sortedCoordinates hH hn u i‖^2 := by
    rw [← sortedCoordinates_sq_norm hH hn,sortedCoordinates_sub]
    calc
      ∑ j : Fin n, ‖(sortedCoordinates hH hn u-sortedCoordinates hH hn (erase hH hn u i)) j‖^2 =
          ∑ j : Fin n, if j=i then ‖sortedCoordinates hH hn u i‖^2 else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hji : j=i
        · subst j
          simp [Pi.sub_apply,erase_self,sub_zero]
        · simp only [Pi.sub_apply,erase_other hH hn u hji,sub_self,norm_zero,
            zero_pow (by decide : 2≠0),if_neg hji]
      _ = ‖sortedCoordinates hH hn u i‖^2 := by simp
  nlinarith only [hs,norm_nonneg (u-erase hH hn u i),norm_nonneg (sortedCoordinates hH hn u i)]

end BB.Euclidean
