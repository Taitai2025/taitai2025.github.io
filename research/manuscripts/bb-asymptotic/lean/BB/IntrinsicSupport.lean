import BB.SpectralPVM

/-!
# The intrinsic spectral probability has the proved active support

This identifies support on the actual spectrum with the interval realization
used in the active convergence theorem. Thus changing the carrier introduces
no additional active spectral points and no extra rate hypothesis.
-/

noncomputable section
namespace BB
open MeasureTheory Set

theorem measureSupport_map_closed_subtype (S : Set ℝ) (hS : IsClosed S) (μ : Measure S) :
    Subtype.val '' measureSupport μ = measureSupport (Measure.map (Subtype.val : S → ℝ) μ) := by
  apply subset_antisymm
  · rintro x ⟨t,ht,rfl⟩ U hU htU hzero
    apply ht (Subtype.val ⁻¹' U) (hU.preimage continuous_subtype_val) htU
    rwa [Measure.map_apply measurable_subtype_coe hU.measurableSet] at hzero
  · intro x hx
    have hxS : x ∈ S := by
      by_contra hn
      apply hx Sᶜ hS.isOpen_compl hn
      rw [Measure.map_apply measurable_subtype_coe hS.measurableSet.compl]
      have hempty : (Subtype.val : S → ℝ) ⁻¹' Sᶜ = ∅ := by
        ext t
        simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false]
        exact iff_false_intro (not_not.mpr t.2)
      rw [hempty, measure_empty]
    refine ⟨⟨x,hxS⟩, ?_, rfl⟩
    intro U hU hxU hzero
    obtain ⟨V,hV,hVU⟩ := isOpen_induced_iff.mp hU
    apply hx V hV
    · change (⟨x,hxS⟩ : S) ∈ Subtype.val ⁻¹' V
      rw [hVU]
      exact hxU
    · rw [Measure.map_apply measurable_subtype_coe hV.measurableSet, hVU]
      exact hzero

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (A x) ∧
    inner (𝕜 := ℝ) x (A x) ≤ b*‖x‖^2)

/-- The support of the actual-spectrum probability, included in ℝ, is exactly
the active support already used by the sharp convergence theorem. -/
theorem operator_intrinsic_spectral_support (x : E) (hx : x ≠ 0) :
    Subtype.val '' measureSupport
      (operatorIntrinsicSpectralProbability A hA a b hbounds x hx : Measure (spectrum ℝ A)) =
      operatorActiveSupport A hA a b hbounds x hx := by
  rw [measureSupport_map_closed_subtype (spectrum ℝ A) (spectrum.isClosed A),
    operator_intrinsic_spectral_probability_map]
  change measureSupport (Measure.map Subtype.val
    (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))) = _
  exact (measureSupport_map_closed_subtype (Icc a b) isClosed_Icc _).symm

end BB
