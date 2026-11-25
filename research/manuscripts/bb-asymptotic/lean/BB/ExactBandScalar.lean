import BB.BandScalar

/-!
# An exact sufficiently narrow endpoint-band certificate

For a fixed positive nondegenerate interval, full endpoint bands can be chosen
so narrow that their weighted multiplier product is bounded by the exact
endpoint rate, with equality only at the midpoint. This strengthens the
manuscript's limiting scalar estimate and is proved by a three-region split.
-/

noncomputable section
namespace BB
open Set
open scoped Topology

def lowerBandFactor (a δ u : ℝ) : ℝ := max (u-a) (a+δ-u) / u
def upperBandFactor (b δ u : ℝ) : ℝ := max (b-u) (u-b+δ) / u
def exactBandProduct (a b δ u : ℝ) : ℝ :=
  lowerBandFactor a δ u ^ leftWeight a b * upperBandFactor b δ u ^ rightWeight a b

def exactBandLog (a b δ u : ℝ) : ℝ :=
  leftWeight a b * Real.log (lowerBandFactor a δ u) +
    rightWeight a b * Real.log (upperBandFactor b δ u)

lemma lowerBandFactor_pos {a δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) :
    0 < lowerBandFactor a δ u := by
  apply div_pos _ hu
  have h₁ := le_max_left (u-a) (a+δ-u)
  have h₂ := le_max_right (u-a) (a+δ-u)
  linarith

lemma upperBandFactor_pos {b δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) :
    0 < upperBandFactor b δ u := by
  apply div_pos _ hu
  have h₁ := le_max_left (b-u) (u-b+δ)
  have h₂ := le_max_right (b-u) (u-b+δ)
  linarith

lemma exactBandProduct_pos {a b δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) :
    0 < exactBandProduct a b δ u :=
  mul_pos (Real.rpow_pos_of_pos (lowerBandFactor_pos hδ hu) _)
    (Real.rpow_pos_of_pos (upperBandFactor_pos hδ hu) _)

lemma exact_band_log_eq_log_product {a b δ u : ℝ} (hδ : 0 < δ) (hu : 0 < u) :
    exactBandLog a b δ u = Real.log (exactBandProduct a b δ u) := by
  rw [exactBandProduct,Real.log_mul (Real.rpow_pos_of_pos (lowerBandFactor_pos hδ hu) _).ne'
    (Real.rpow_pos_of_pos (upperBandFactor_pos hδ hu) _).ne',
    Real.log_rpow (lowerBandFactor_pos hδ hu),Real.log_rpow (upperBandFactor_pos hδ hu)]
  rfl

lemma lower_band_factor_bound {a δ u ell : ℝ} (hu : 0 < u)
    (hella : a ≤ ell) (hellδ : ell ≤ a+δ) :
    |1-ell/u| ≤ lowerBandFactor a δ u := by
  have hnum : |u-ell| ≤ max (u-a) (a+δ-u) := by
    apply abs_le.mpr
    constructor
    · have h := le_max_right (u-a) (a+δ-u)
      linarith
    · exact (sub_le_sub_left hella u).trans (le_max_left _ _)
  rw [← div_self hu.ne', ← sub_div, abs_div, abs_of_pos hu]
  exact (div_le_div_right hu).mpr hnum

lemma upper_band_factor_bound {b δ u ell : ℝ} (hu : 0 < u)
    (hellδ : b-δ ≤ ell) (hellb : ell ≤ b) :
    |1-ell/u| ≤ upperBandFactor b δ u := by
  have hnum : |u-ell| ≤ max (b-u) (u-b+δ) := by
    apply abs_le.mpr
    constructor
    · have h := le_max_left (b-u) (u-b+δ)
      linarith
    · have h := le_max_right (b-u) (u-b+δ)
      linarith
  rw [← div_self hu.ne', ← sub_div, abs_div, abs_of_pos hu]
  exact (div_le_div_right hu).mpr hnum

lemma exact_band_product_central {a b δ u : ℝ}
    (hlo : a+δ/2 ≤ u) (hhi : u ≤ b-δ/2) :
    exactBandProduct a b δ u = endpointProduct a b u := by
  unfold exactBandProduct lowerBandFactor upperBandFactor endpointProduct
  rw [max_eq_left (by linarith),max_eq_left (by linarith)]

lemma exact_band_product_lower_region {a b δ u : ℝ}
    (ha : 0 < a) (hab : a < b) (hδ : 0 ≤ δ) (hδd : δ < (b-a)/2)
    (hau : a ≤ u) (hul : u ≤ a+δ/2) :
    exactBandProduct a b δ u ≤
      (δ/a)^leftWeight a b * ((b-a)/a)^rightWeight a b := by
  have hu : 0 < u := ha.trans_le hau
  have hL : lowerBandFactor a δ u = (a+δ-u)/u := by
    unfold lowerBandFactor
    rw [max_eq_right (by linarith)]
  have hU : upperBandFactor b δ u = (b-u)/u := by
    unfold upperBandFactor
    rw [max_eq_left (by linarith)]
  have hL0 : 0 ≤ (a+δ-u)/u := div_nonneg (by linarith) hu.le
  have hU0 : 0 ≤ (b-u)/u := div_nonneg (by linarith) hu.le
  have hLa : (a+δ-u)/u ≤ δ/a := by
    apply (div_le_div_iff hu ha).mpr
    nlinarith only [mul_nonneg (add_nonneg ha.le hδ) (sub_nonneg.mpr hau)]
  have hUa : (b-u)/u ≤ (b-a)/a := by
    apply (div_le_div_iff hu ha).mpr
    nlinarith only [mul_nonneg (ha.trans hab).le (sub_nonneg.mpr hau)]
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  unfold exactBandProduct
  rw [hL,hU]
  exact mul_le_mul (Real.rpow_le_rpow hL0 hLa hp.le)
    (Real.rpow_le_rpow hU0 hUa hq.le)
    (Real.rpow_nonneg hU0 _) (Real.rpow_nonneg (div_nonneg hδ ha.le) _)

lemma exact_band_product_upper_region {a b δ u : ℝ}
    (ha : 0 < a) (hab : a < b) (hδ : 0 ≤ δ) (hδd : δ < (b-a)/2)
    (hub : u ≤ b) (hhu : b-δ/2 ≤ u) :
    exactBandProduct a b δ u ≤
      ((b-a)/b)^leftWeight a b * (δ/b)^rightWeight a b := by
  have hau : a ≤ u := by linarith
  have hu : 0 < u := ha.trans_le hau
  have hb : 0 < b := ha.trans hab
  have hL : lowerBandFactor a δ u = (u-a)/u := by
    unfold lowerBandFactor
    rw [max_eq_left (by linarith)]
  have hU : upperBandFactor b δ u = (u-b+δ)/u := by
    unfold upperBandFactor
    rw [max_eq_right (by linarith)]
  have hL0 : 0 ≤ (u-a)/u := div_nonneg (sub_nonneg.mpr hau) hu.le
  have hU0 : 0 ≤ (u-b+δ)/u := div_nonneg (by linarith) hu.le
  have hLb : (u-a)/u ≤ (b-a)/b := by
    apply (div_le_div_iff hu hb).mpr
    nlinarith only [mul_nonneg ha.le (sub_nonneg.mpr hub)]
  have hUb : (u-b+δ)/u ≤ δ/b := by
    apply (div_le_div_iff hu hb).mpr
    have hbd : 0 ≤ b-δ := by linarith
    nlinarith only [mul_nonneg hbd (sub_nonneg.mpr hub)]
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  unfold exactBandProduct
  rw [hL,hU]
  exact mul_le_mul (Real.rpow_le_rpow hL0 hLb hp.le)
    (Real.rpow_le_rpow hU0 hUb hq.le)
    (Real.rpow_nonneg hU0 _) (Real.rpow_nonneg (div_nonneg (sub_nonneg.mpr hab.le) hb.le) _)

lemma exact_band_certificate_of_edges {a b δ : ℝ} (ha : 0 < a) (hab : a < b)
    (hδ : 0 ≤ δ) (hδd : δ < (b-a)/2)
    (hlow : (δ/a)^leftWeight a b * ((b-a)/a)^rightWeight a b < rate a b)
    (hhigh : ((b-a)/b)^leftWeight a b * (δ/b)^rightWeight a b < rate a b) :
    ∀ u ∈ Icc a b, exactBandProduct a b δ u ≤ rate a b ∧
      (exactBandProduct a b δ u = rate a b ↔ u = (a+b)/2) := by
  intro u hu
  by_cases hlo : u ≤ a+δ/2
  · have hlt := (exact_band_product_lower_region ha hab hδ hδd hu.1 hlo).trans_lt hlow
    have hne : u ≠ (a+b)/2 := by intro h; rw [h] at hlo; linarith
    exact ⟨hlt.le,iff_of_false hlt.ne hne⟩
  · by_cases hhi : b-δ/2 ≤ u
    · have hlt := (exact_band_product_upper_region ha hab hδ hδd hu.2 hhi).trans_lt hhigh
      have hne : u ≠ (a+b)/2 := by intro h; rw [h] at hhi; linarith
      exact ⟨hlt.le,iff_of_false hlt.ne hne⟩
    · rw [exact_band_product_central (le_of_lt (lt_of_not_ge hlo)) (le_of_lt (lt_of_not_ge hhi))]
      exact ⟨endpoint_product_le ha hab hu,endpoint_product_eq_iff ha hab hu⟩

/-- A single strictly positive band width gives the exact sharp rate and the
same unique midpoint equality case, including at both interval endpoints. -/
theorem exists_exact_endpoint_band (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ δ : ℝ, 0 < δ ∧ δ < (b-a)/2 ∧
      ∀ u ∈ Icc a b, exactBandProduct a b δ u ≤ rate a b ∧
        (exactBandProduct a b δ u = rate a b ↔ u = (a+b)/2) := by
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  let low : ℝ → ℝ := fun δ => (δ/a)^leftWeight a b * ((b-a)/a)^rightWeight a b
  let high : ℝ → ℝ := fun δ => ((b-a)/b)^leftWeight a b * (δ/b)^rightWeight a b
  have hlow : Continuous low :=
    ((continuous_id.div_const a).rpow_const (fun _ => Or.inr hp.le)).mul continuous_const
  have hhigh : Continuous high :=
    continuous_const.mul ((continuous_id.div_const b).rpow_const (fun _ => Or.inr hq.le))
  let U : Set ℝ := {δ | δ < (b-a)/2 ∧ low δ < rate a b ∧ high δ < rate a b}
  have hU : IsOpen U := (isOpen_lt continuous_id continuous_const).inter
    ((isOpen_lt hlow continuous_const).inter (isOpen_lt hhigh continuous_const))
  have h0 : (0:ℝ) ∈ U := by
    change 0 < (b-a)/2 ∧ low 0 < rate a b ∧ high 0 < rate a b
    simp only [low,high,zero_div,Real.zero_rpow hp.ne',Real.zero_rpow hq.ne',zero_mul,mul_zero]
    exact ⟨by linarith,rate_pos ha hab,rate_pos ha hab⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU 0 h0
  have hδU : ε/2 ∈ U := hball (by
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
    linarith)
  exact ⟨ε/2,half_pos hε,hδU.1,
    exact_band_certificate_of_edges ha hab (half_pos hε).le hδU.1 hδU.2.1 hδU.2.2⟩

lemma exact_band_product_mono_width {a b δ ε u : ℝ}
    (ha : 0 < a) (hab : a < b) (hεδ : ε ≤ δ)
    (hu : u ∈ Icc a b) : exactBandProduct a b ε u ≤ exactBandProduct a b δ u := by
  have hu0 : 0 < u := ha.trans_le hu.1
  have hL0 : 0 ≤ lowerBandFactor a ε u :=
    div_nonneg ((sub_nonneg.mpr hu.1).trans (le_max_left _ _)) hu0.le
  have hU0 : 0 ≤ upperBandFactor b ε u :=
    div_nonneg ((sub_nonneg.mpr hu.2).trans (le_max_left _ _)) hu0.le
  have hL : lowerBandFactor a ε u ≤ lowerBandFactor a δ u := by
    apply (div_le_div_right hu0).mpr
    exact max_le_max le_rfl (by linarith)
  have hU : upperBandFactor b ε u ≤ upperBandFactor b δ u := by
    apply (div_le_div_right hu0).mpr
    exact max_le_max le_rfl (by linarith)
  obtain ⟨hp,hq⟩ := endpoint_weights_pos ha hab
  exact mul_le_mul (Real.rpow_le_rpow hL0 hL hp.le)
    (Real.rpow_le_rpow hU0 hU hq.le) (Real.rpow_nonneg hU0 _)
    (Real.rpow_nonneg (hL0.trans hL) _)

lemma exact_band_product_continuousOn (a b δ : ℝ) (ha : 0 < a) (hδ : 0 < δ) :
    ContinuousOn (exactBandProduct a b δ) (Icc a b) := by
  have hL : ContinuousOn (lowerBandFactor a δ) (Icc a b) :=
    ((continuous_id.sub continuous_const).max (continuous_const.sub continuous_id)).continuousOn.div
      continuous_id.continuousOn (fun u hu => (ha.trans_le hu.1).ne')
  have hU : ContinuousOn (upperBandFactor b δ) (Icc a b) :=
    ((continuous_const.sub continuous_id).max
      ((continuous_id.sub continuous_const).add continuous_const)).continuousOn.div
      continuous_id.continuousOn (fun u hu => (ha.trans_le hu.1).ne')
  exact (hL.rpow_const (fun u hu => Or.inl (lowerBandFactor_pos hδ (ha.trans_le hu.1)).ne')).mul
    (hU.rpow_const (fun u hu => Or.inl (upperBandFactor_pos hδ (ha.trans_le hu.1)).ne'))

end BB
