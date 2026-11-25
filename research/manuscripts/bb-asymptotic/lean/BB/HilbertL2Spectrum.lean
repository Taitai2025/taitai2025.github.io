import BB.HilbertL2Example
import BB.ApproxEigen

/-!
# Exact spectrum of interval multiplication

Localized interval indicators give nonzero approximate eigenvectors at every
point of `[a,b]`. Outside that interval the quadratic-form bounds and
Lax--Milgram exclude spectral values. No spectral representation theorem is
assumed in this example.
-/

namespace BB
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal

lemma interval_shift_coe (a b ell : ℝ) (f : intervalL2 a b) :
    ⇑((algebraMap ℝ (intervalL2 a b →L[ℝ] intervalL2 a b) ell - intervalMultiplication a b) f)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => (ell-t)*f t := by
  simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  filter_upwards [Lp.coeFn_sub (ell • f) (intervalMultiplication a b f),
    Lp.coeFn_smul ell f, interval_multiplication_coe a b f] with t h1 h2 h3
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
  change ell*f t - intervalMultiplicationLinear a b f t = _
  rw [h3]
  ring

lemma interval_localized_residual (a b ell δ : ℝ) (hab : a < b)
    (hell : ell ∈ Set.Icc a b) (hδ : 0 < δ) :
    ∃ f : intervalL2 a b, 0 < ‖f‖ ∧
      ‖(algebraMap ℝ (intervalL2 a b →L[ℝ] intervalL2 a b) ell -
        intervalMultiplication a b) f‖ ≤ δ*‖f‖ := by
  let u := max a (ell-δ)
  let v := min b (ell+δ)
  have huv : u < v := by
    dsimp [u, v]
    rw [max_lt_iff, lt_min_iff, lt_min_iff]
    exact ⟨⟨hab, by linarith [hell.1]⟩, ⟨by linarith [hell.2], by linarith⟩⟩
  have hsub : Set.Icc u v ⊆ Set.Icc a b := by
    intro t ht
    exact ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have hvol : (volume.restrict (Set.Icc a b)) (Set.Icc u v) = ENNReal.ofReal (v-u) := by
    rw [Measure.restrict_apply measurableSet_Icc, Set.inter_eq_left.mpr hsub, Real.volume_Icc]
  have hfin : (volume.restrict (Set.Icc a b)) (Set.Icc u v) ≠ ∞ := by
    rw [hvol]
    exact ENNReal.ofReal_ne_top
  let f : intervalL2 a b := indicatorConstLp 2 measurableSet_Icc hfin (1:ℝ)
  have hfcoe : ⇑f =ᵐ[volume.restrict (Set.Icc a b)] (Set.Icc u v).indicator (fun _ => (1:ℝ)) :=
    indicatorConstLp_coeFn
  have hfpos : 0 < ‖f‖ := by
    dsimp [f]
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), hvol]
    simp only [norm_one, one_mul, ENNReal.toReal_ofReal (sub_nonneg.mpr huv.le)]
    exact Real.rpow_pos_of_pos (sub_pos.mpr huv) _
  refine ⟨f, hfpos, ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [interval_shift_coe a b ell f, hfcoe] with t hT hf
  rw [hT, norm_mul, Real.norm_eq_abs]
  by_cases ht : t ∈ Set.Icc u v
  · have hlo : ell-δ ≤ t := (le_max_right _ _).trans ht.1
    have hhi : t ≤ ell+δ := ht.2.trans (min_le_right _ _)
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith, by linarith⟩) (norm_nonneg _)
  · rw [hf, Set.indicator_of_not_mem ht, norm_zero, mul_zero, mul_zero]

theorem interval_multiplication_spectrum (a b : ℝ) (hab : a < b) :
    spectrum ℝ (intervalMultiplication a b) = Set.Icc a b := by
  ext ell
  constructor
  · intro hs
    constructor
    · by_contra h
      obtain ⟨x,hx,hRay⟩ := spectrum_lower_rayleigh (intervalMultiplication a b) ell
        ((a-ell)/2) hs (by linarith)
      have hbound := (interval_multiplication_form_bounds a b x).1
      rw [hx, one_pow, mul_one] at hbound
      linarith
    · by_contra h
      obtain ⟨x,hx,hRay⟩ := spectrum_upper_rayleigh (intervalMultiplication a b) ell
        ((ell-b)/2) hs (by linarith)
      have hbound := (interval_multiplication_form_bounds a b x).2
      rw [hx, one_pow, mul_one] at hbound
      linarith
  · intro hell
    apply spectrum.mem_iff.mpr
    rintro ⟨u, hu⟩
    let R : intervalL2 a b →L[ℝ] intervalL2 a b := ↑(u⁻¹)
    let δ : ℝ := (2*(‖R‖+1))⁻¹
    have hδ : 0 < δ := inv_pos.mpr (by positivity)
    obtain ⟨f,hf,hres⟩ := interval_localized_residual a b ell δ hab hell hδ
    have hrecover : R ((algebraMap ℝ (intervalL2 a b →L[ℝ] intervalL2 a b) ell -
        intervalMultiplication a b) f) = f := by
      rw [← hu]
      change (↑(u⁻¹) : intervalL2 a b →L[ℝ] intervalL2 a b)
        ((u : intervalL2 a b →L[ℝ] intervalL2 a b) f) = f
      rw [← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply]
    have hn := R.le_opNorm ((algebraMap ℝ (intervalL2 a b →L[ℝ] intervalL2 a b) ell -
      intervalMultiplication a b) f)
    rw [hrecover] at hn
    have hprod := mul_le_mul_of_nonneg_left hres (norm_nonneg R)
    have hδprod : (2*(‖R‖+1))*δ = 1 := mul_inv_cancel (by positivity)
    have hsmall : ‖R‖*δ < 1 := by nlinarith [norm_nonneg R]
    have hstrict := mul_lt_mul_of_pos_right hsmall hf
    nlinarith

end
end BB
