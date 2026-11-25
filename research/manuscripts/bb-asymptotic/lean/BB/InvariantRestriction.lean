import BB.InvariantPartition

/-!
# Finite invariant restrictions and strict components

Normalization transfers an invariant probability bound to every finite
invariant measure. Exact two-piece averaging then excludes a positive-mass
invariant component whose bound is strictly smaller than a maximal mean.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

lemma invariant_finite_bound_of_probability_bound (T : X → X) (P : X → Prop)
    (f : X → ℝ) (β : ℝ)
    (hprob : ∀ (ν : Measure X), IsProbabilityMeasure ν → MeasurePreserving T ν ν →
      (∀ᵐ x ∂ν, P x) → Integrable f ν → (∫ x, f x ∂ν) ≤ β)
    (μ : Measure X) [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ)
    (hP : ∀ᵐ x ∂μ, P x) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) ≤ (μ univ).toReal * β := by
  by_cases hμ : μ = 0
  · subst μ
    simp
  · have hm : μ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr hμ
    have hmfin : μ univ ≠ ∞ := measure_ne_top μ univ
    let ν : Measure X := (μ univ)⁻¹ • μ
    have hνprob : IsProbabilityMeasure ν := by
      constructor
      change (μ univ)⁻¹ * μ univ = 1
      exact ENNReal.inv_mul_cancel hm hmfin
    have hνT : MeasurePreserving T ν ν := ⟨hT.measurable,by
      change Measure.map T ((μ univ)⁻¹ • μ) = (μ univ)⁻¹ • μ
      rw [Measure.map_smul,hT.map_eq]⟩
    have hνP : ∀ᵐ x ∂ν, P x :=
      (Measure.ae_smul_measure_iff (ENNReal.inv_ne_zero.mpr hmfin)).mpr hP
    have hνf : Integrable f ν := hf.smul_measure (ENNReal.inv_ne_top.mpr hm)
    have hbound := hprob ν hνprob hνT hνP hνf
    have hmass : 0 < (μ univ).toReal := ENNReal.toReal_pos hm hmfin
    change (∫ x, f x ∂((μ univ)⁻¹ • μ)) ≤ β at hbound
    rw [integral_smul_measure,ENNReal.toReal_inv,smul_eq_mul] at hbound
    calc
      (∫ x, f x ∂μ) = (μ univ).toReal * ((μ univ).toReal⁻¹ * (∫ x, f x ∂μ)) := by
        rw [← mul_assoc,mul_inv_cancel hmass.ne',one_mul]
      _ ≤ (μ univ).toReal * β := mul_le_mul_of_nonneg_left hbound hmass.le

lemma strict_component_null_of_maximal_mean (μ : Measure X) [IsProbabilityMeasure μ]
    (A : Set X) (hA : MeasurableSet A) (f : X → ℝ) (hf : Integrable f μ)
    (β α : ℝ) (hαβ : α < β) (hmaximal : (∫ x, f x ∂μ) = β)
    (hpart : (∫ x in A, f x ∂μ) ≤ (μ A).toReal * α)
    (hcompl : (∫ x in Aᶜ, f x ∂μ) ≤ (μ Aᶜ).toReal * β) : μ A = 0 := by
  have hsum := integral_add_compl hA hf
  rw [hmaximal] at hsum
  have hmasssum : (μ A).toReal + (μ Aᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top μ A) (measure_ne_top μ Aᶜ),
      prob_add_prob_compl hA,ENNReal.one_toReal]
  have hzero : (μ A).toReal = 0 := by
    have hnonneg : 0 ≤ (μ A).toReal := ENNReal.toReal_nonneg
    apply le_antisymm ?_ hnonneg
    by_contra hn
    have hp := mul_pos (lt_of_not_ge hn) (sub_pos.mpr hαβ)
    have hm := congrArg (fun x : ℝ => x * β) hmasssum
    simp only [add_mul,one_mul] at hm
    nlinarith only [hsum,hm,hpart,hcompl,hp]
  exact (ENNReal.toReal_eq_zero_iff (μ A)).mp hzero |>.resolve_right (measure_ne_top μ A)

end BB
