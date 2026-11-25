import BB.SpectralPVM
import BB.DistinctActive

/-!
# The finite active spectrum equals the nonzero spectral projections

Repeated eigenvalues may have several basis coordinates.  The actual singleton
spectral projection keeps precisely those coordinates, so grouping by active
eigenvalues is exactly the basis-independent definition in the manuscript.
-/

noncomputable section
namespace BB
open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
    inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)

theorem finite_spectral_projection_basis (r : ℝ)
    (i : Fin (FiniteDimensional.finrank ℝ E)) :
    (operatorSpectralPVM A hA a b hbounds).map {r} (measurableSet_singleton r)
      (hA.eigenvectorBasis rfl i) =
      if eigenValues hA i=r then hA.eigenvectorBasis rfl i else 0 := by
  classical
  let t : Icc a b := ⟨eigenValues hA i,eigenvalue_bounds hA a b hbounds i⟩
  have hev : A (hA.eigenvectorBasis rfl i) = (t : ℝ) • hA.eigenvectorBasis rfl i :=
    hA.apply_eigenvectorBasis rfl i
  rw [operator_spectral_pvm_apply]
  have hp := spectral_projection_eigenvector A hA a b hbounds
    (Subtype.val ⁻¹' {r}) ((measurableSet_singleton r).preimage measurable_subtype_coe)
    t (hA.eigenvectorBasis rfl i) hev
  simpa only [Set.indicator_apply,mem_preimage,mem_singleton_iff,t,ite_smul,one_smul,zero_smul]
    using hp

theorem finite_spectral_projection_coordinates (r : ℝ) (g : E)
    (i : Fin (FiniteDimensional.finrank ℝ E)) :
    eigenCoordinates hA ((operatorSpectralPVM A hA a b hbounds).map {r}
      (measurableSet_singleton r) g) i =
      if eigenValues hA i=r then eigenCoordinates hA g i else 0 := by
  classical
  let P := (operatorSpectralPVM A hA a b hbounds).map {r} (measurableSet_singleton r)
  have hs := (operatorSpectralPVM A hA a b hbounds).symmetric {r} (measurableSet_singleton r)
  simp only [eigenCoordinates,OrthonormalBasis.repr_apply_apply]
  calc
    _ = inner (𝕜 := ℝ) (P (hA.eigenvectorBasis rfl i)) g := (hs _ _).symm
    _ = _ := by
      dsimp only [P]
      rw [finite_spectral_projection_basis A hA a b hbounds r i]
      split_ifs <;> simp

theorem finite_spectral_projection_zero_iff (r : ℝ) (g : E) :
    (operatorSpectralPVM A hA a b hbounds).map {r} (measurableSet_singleton r) g=0 ↔
      ∀ i, eigenValues hA i=r → eigenCoordinates hA g i=0 := by
  classical
  constructor
  · intro hz i hi
    have he := congrArg (fun x => eigenCoordinates hA x i) hz
    dsimp only at he
    rw [finite_spectral_projection_coordinates A hA a b hbounds r g i,if_pos hi] at he
    simpa only [eigenCoordinates,map_zero,PiLp.zero_apply] using he
  · intro h
    apply eigen_coordinates_injective hA
    funext i
    rw [finite_spectral_projection_coordinates A hA a b hbounds r g i]
    by_cases hi : eigenValues hA i=r
    · rw [if_pos hi,h i hi]
      simp only [eigenCoordinates,map_zero,PiLp.zero_apply]
    · simp only [if_neg hi,eigenCoordinates,map_zero,PiLp.zero_apply]

theorem finite_spectral_projection_ne_zero_iff (r : ℝ) (g : E) :
    (operatorSpectralPVM A hA a b hbounds).map {r} (measurableSet_singleton r) g ≠ 0 ↔
      ∃ i, eigenValues hA i=r ∧ eigenCoordinates hA g i≠0 := by
  rw [ne_eq,finite_spectral_projection_zero_iff A hA a b hbounds r g]
  simp only [not_forall,_root_.not_imp,exists_prop,ne_eq]

theorem finite_active_values_eq_projection_spectrum (g : E) :
    (↑(activeValues (eigenValues hA) (eigenCoordinates hA g)) : Set ℝ) =
      {r ∈ spectrum ℝ A | (operatorSpectralPVM A hA a b hbounds).map {r}
        (measurableSet_singleton r) g ≠ 0} := by
  classical
  ext r
  have he : r ∈ activeValues (eigenValues hA) (eigenCoordinates hA g) ↔
      ∃ i, eigenValues hA i=r ∧ eigenCoordinates hA g i≠0 := by
    simp only [activeValues,Finset.mem_image,coordinateSupport,Finset.mem_filter,
      Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hg,hi⟩
      exact ⟨i,hi,hg⟩
    · rintro ⟨i,hi,hg⟩
      exact ⟨i,hg,hi⟩
  change r ∈ activeValues (eigenValues hA) (eigenCoordinates hA g) ↔ _
  rw [he,← finite_spectral_projection_ne_zero_iff A hA a b hbounds r g]
  constructor
  · intro hn
    refine ⟨?_,hn⟩
    by_contra hspec
    have hz := operator_spectral_pvm_outside_spectrum A hA a b hbounds {r}
      (measurableSet_singleton r) (by simpa only [disjoint_singleton_left] using hspec)
    exact hn (by rw [hz]; rfl)
  · exact fun h => h.2

end BB
