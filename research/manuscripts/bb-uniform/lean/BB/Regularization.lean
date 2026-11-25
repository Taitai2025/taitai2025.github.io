import BB.Endpoint
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section

namespace BB

open Real

/-- Positive clipping thresholds exist for every positive endpoint exponent. -/
theorem exists_clipping_threshold {A θ : ℝ} (hA : 1 ≤ A) (hθ : 0 < θ) (hθ' : θ < 1) :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ A * d ^ θ ≤ 1 ∧ A * d ^ (1 - θ) ≤ 1 := by
  have hAp : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hc : 0 < 1 - θ := sub_pos.mpr hθ'
  let d := min 1 (min (A ^ (-1 / θ)) (A ^ (-1 / (1 - θ))))
  have hd : 0 < d := lt_min zero_lt_one (lt_min (Real.rpow_pos_of_pos hAp _) (Real.rpow_pos_of_pos hAp _))
  refine ⟨d, hd, min_le_left _ _, ?_, ?_⟩
  · have hle : d ≤ A ^ (-1 / θ) := (min_le_right _ _).trans (min_le_left _ _)
    calc
      A * d ^ θ ≤ A * (A ^ (-1 / θ)) ^ θ :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le hle hθ.le) hAp.le
      _ = 1 := by
        rw [← Real.rpow_mul hAp.le, div_mul_cancel₀ _ hθ.ne', Real.rpow_neg_one]
        exact mul_inv_cancel hAp.ne'
  · have hle : d ≤ A ^ (-1 / (1 - θ)) := (min_le_right _ _).trans (min_le_right _ _)
    calc
      A * d ^ (1 - θ) ≤ A * (A ^ (-1 / (1 - θ))) ^ (1 - θ) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hd.le hle hc.le) hAp.le
      _ = 1 := by
        rw [← Real.rpow_mul hAp.le, div_mul_cancel₀ _ hc.ne', Real.rpow_neg_one]
        exact mul_inv_cancel hAp.ne'

/-- Weighted AM-GM gives an explicit affine upper bound based at positive coordinates. -/
theorem geometricProduct_tangent {θ x y u v : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1)
    (hx : 0 < x) (hy : 0 < y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    geometricProduct θ u v ≤ geometricProduct θ x y * (θ * (u / x) + (1 - θ) * (v / y)) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hθ (sub_nonneg.mpr hθ')
    (div_nonneg hu hx.le) (div_nonneg hv hy.le) (by ring : θ + (1 - θ) = 1)
  have heq : geometricProduct θ u v =
      geometricProduct θ x y * geometricProduct θ (u / x) (v / y) := by
    rw [← geometricProduct_mul hx.le hy.le (div_nonneg hu hx.le) (div_nonneg hv hy.le)]
    congr 1 <;> field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left h (geometricProduct_nonneg hx.le hy.le)

/-- The clipping operation leaves the maximum unchanged. -/
theorem regularization_clipping_identity {A θ d r x y : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hd : 0 ≤ d) (hd1 : d ≤ 1)
    (hAdx : A * d ^ θ ≤ 1) (hAdy : A * d ^ (1 - θ) ≤ 1)
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxr : x ≤ r) (hyr : y ≤ r) :
    max r (A * geometricProduct θ x y) =
      max r (A * geometricProduct θ (max x (d * r)) (max y (d * r))) := by
  have hdr : d * r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hr
  have hyclip : max y (d * r) ≤ r := max_le hyr hdr
  by_cases hdx : d * r ≤ x
  · rw [max_eq_left hdx]
    by_cases hdy : d * r ≤ y
    · rw [max_eq_left hdy]
    · have hylt : y ≤ d * r := le_of_lt (lt_of_not_ge hdy)
      rw [max_eq_right hylt]
      have hbound : A * geometricProduct θ x (d * r) ≤ r := by
        calc
          A * geometricProduct θ x (d * r) ≤ A * geometricProduct θ r (d * r) :=
            mul_le_mul_of_nonneg_left
              (geometricProduct_mono hθ hθ' hx (mul_nonneg hd hr) hxr le_rfl) hA
          _ = (A * d ^ (1 - θ)) * r := by
            have hid := geometricProduct_homogeneous hθ hθ' hr (by norm_num : (0:ℝ) ≤ 1) hd
            simp only [mul_one, geometricProduct, Real.one_rpow] at hid
            rw [mul_comm d r]
            unfold geometricProduct
            rw [hid]
            ring
          _ ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hAdy hr
      have hold : A * geometricProduct θ x y ≤ r :=
        (mul_le_mul_of_nonneg_left
          (geometricProduct_mono hθ hθ' hx hy le_rfl hylt) hA).trans hbound
      rw [max_eq_left hold, max_eq_left hbound]
  · have hxlt : x ≤ d * r := le_of_lt (lt_of_not_ge hdx)
    rw [max_eq_right hxlt]
    have hbound : A * geometricProduct θ (d * r) (max y (d * r)) ≤ r := by
      calc
        A * geometricProduct θ (d * r) (max y (d * r)) ≤ A * geometricProduct θ (d * r) r :=
          mul_le_mul_of_nonneg_left
            (geometricProduct_mono hθ hθ' (mul_nonneg hd hr) (hy.trans (le_max_left _ _))
              le_rfl hyclip) hA
        _ = (A * d ^ θ) * r := by
          have hid := geometricProduct_homogeneous hθ hθ' hr hd (by norm_num : (0:ℝ) ≤ 1)
          simp only [mul_one, geometricProduct, Real.one_rpow] at hid
          rw [mul_comm d r]
          unfold geometricProduct
          rw [hid]
          ring
        _ ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hAdx hr
    have hold : A * geometricProduct θ x y ≤ r :=
      (mul_le_mul_of_nonneg_left
        (geometricProduct_mono hθ hθ' hx hy hxlt (le_max_left _ _)) hA).trans hbound
    rw [max_eq_left hold, max_eq_left hbound]


/-- A tangent bound remains uniformly controlled when both coordinates exceed d times a common scale. -/
theorem geometricProduct_difference_le {θ d r x y u v : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hr : 0 ≤ r) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxr : x ≤ r) (hyr : y ≤ r)
    (hdx : d * r ≤ x) (hdy : d * r ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    geometricProduct θ u v - geometricProduct θ x y ≤
      (1 / d) * (|u - x| + |v - y|) := by
  by_cases hr0 : r = 0
  · have hx0 : x = 0 := le_antisymm (by simpa only [hr0] using hxr) hx
    have hy0 : y = 0 := le_antisymm (by simpa only [hr0] using hyr) hy
    rw [hx0, hy0, geometricProduct_self hθ hθ' (le_refl (0:ℝ)), sub_zero,
      sub_zero, sub_zero, abs_of_nonneg hu, abs_of_nonneg hv]
    have hp := geometricProduct_le hθ hθ' hu hv (le_add_of_nonneg_right hv) (le_add_of_nonneg_left hu)
    have hinv : 1 ≤ 1 / d := (le_div_iff hd).2 (by simpa using hd1)
    exact hp.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hinv (add_nonneg hu hv))
  have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
  have hxp : 0 < x := (mul_pos hd hrp).trans_le hdx
  have hyp : 0 < y := (mul_pos hd hrp).trans_le hdy
  let P := geometricProduct θ x y
  have hP : 0 ≤ P := geometricProduct_nonneg hx hy
  have hPr : P ≤ r := geometricProduct_le hθ hθ' hx hy hxr hyr
  have hcx0 : 0 ≤ θ * P / x := div_nonneg (mul_nonneg hθ hP) hx
  have hcy0 : 0 ≤ (1 - θ) * P / y := div_nonneg (mul_nonneg (sub_nonneg.mpr hθ') hP) hy
  have hcx : θ * P / x ≤ 1 / d := by
    apply (div_le_iff hxp).2
    have hrx : r ≤ x / d := (le_div_iff hd).2 (by simpa only [mul_comm] using hdx)
    have hθP : θ * P ≤ r := (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ' hP : θ * P ≤ P).trans hPr
    simpa [div_eq_mul_inv, mul_comm] using hθP.trans hrx
  have hcy : (1 - θ) * P / y ≤ 1 / d := by
    apply (div_le_iff hyp).2
    have hry : r ≤ y / d := (le_div_iff hd).2 (by simpa only [mul_comm] using hdy)
    have hθP : (1 - θ) * P ≤ r := (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (sub_le_self (1:ℝ) hθ) hP : (1 - θ) * P ≤ P).trans hPr
    simpa [div_eq_mul_inv, mul_comm] using hθP.trans hry
  have ht := geometricProduct_tangent hθ hθ' hxp hyp hu hv
  have hid : P * (θ * (u / x) + (1 - θ) * (v / y)) - P =
      (θ * P / x) * (u - x) + ((1 - θ) * P / y) * (v - y) := by
    field_simp
    <;> ring
  change geometricProduct θ u v ≤ P * _ at ht
  calc
    geometricProduct θ u v - P ≤ P * (θ * (u / x) + (1 - θ) * (v / y)) - P :=
      sub_le_sub_right ht P
    _ = (θ * P / x) * (u - x) + ((1 - θ) * P / y) * (v - y) := hid
    _ ≤ (θ * P / x) * |u - x| + ((1 - θ) * P / y) * |v - y| :=
      add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hcx0)
        (mul_le_mul_of_nonneg_left (le_abs_self _) hcy0)
    _ ≤ (1 / d) * |u - x| + (1 / d) * |v - y| :=
      add_le_add (mul_le_mul_of_nonneg_right hcx (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hcy (abs_nonneg _))
    _ = (1 / d) * (|u - x| + |v - y|) := by ring

/-- The geometric product is Lipschitz on the double cone d r ≤ x,y ≤ r. -/
theorem geometricProduct_abs_difference_le {θ d r s x y u v : ℝ}
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hxr : x ≤ r) (hyr : y ≤ r) (hus : u ≤ s) (hvs : v ≤ s)
    (hdx : d * r ≤ x) (hdy : d * r ≤ y) (hdu : d * s ≤ u) (hdv : d * s ≤ v) :
    |geometricProduct θ u v - geometricProduct θ x y| ≤
      (1 / d) * (|u - x| + |v - y|) := by
  apply abs_le.mpr
  constructor
  · have h := geometricProduct_difference_le hθ hθ' hd hd1 hs hu hv hus hvs hdu hdv hx hy
    rw [abs_sub_comm x u, abs_sub_comm y v] at h
    linarith only [h]
  · exact geometricProduct_difference_le hθ hθ' hd hd1 hr hx hy hxr hyr hdx hdy hu hv


/-- Clipping two scalar 1-Lipschitz data at d times a third keeps the same bound. -/
theorem clip_abs_difference_le {d r s x u ρ : ℝ}
    (hd : 0 ≤ d) (hd1 : d ≤ 1) (hρ : 0 ≤ ρ)
    (hrs : |r - s| ≤ ρ) (hxu : |x - u| ≤ ρ) :
    |max x (d * r) - max u (d * s)| ≤ ρ := by
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le hxu
  rw [← mul_sub, abs_mul, abs_of_nonneg hd]
  exact (mul_le_mul_of_nonneg_left hrs hd).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hρ)

/-- A completely algebraic Lipschitz estimate for the regularized endpoint product. -/
theorem regularization_abs_difference_le {A θ d r s x y u v ρ : ℝ}
    (hA : 0 ≤ A) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) (hd : 0 < d) (hd1 : d ≤ 1)
    (hAdx : A * d ^ θ ≤ 1) (hAdy : A * d ^ (1 - θ) ≤ 1)
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hxr : x ≤ r) (hyr : y ≤ r) (hus : u ≤ s) (hvs : v ≤ s)
    (hρ : 0 ≤ ρ) (hrs : |r - s| ≤ ρ) (hxu : |x - u| ≤ ρ) (hyv : |y - v| ≤ ρ) :
    |max r (A * geometricProduct θ x y) - max s (A * geometricProduct θ u v)| ≤
      max 1 (2 * A / d) * ρ := by
  rw [regularization_clipping_identity hA hθ hθ' hd.le hd1 hAdx hAdy hr hx hy hxr hyr,
      regularization_clipping_identity hA hθ hθ' hd.le hd1 hAdx hAdy hs hu hv hus hvs]
  have hdr : d * r ≤ r := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hr
  have hds : d * s ≤ s := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hd1 hs
  have hclipx := clip_abs_difference_le hd.le hd1 hρ hrs hxu
  have hclipy := clip_abs_difference_le hd.le hd1 hρ hrs hyv
  have hP := geometricProduct_abs_difference_le hθ hθ' hd hd1 hs hr
    (hu.trans (le_max_left _ _)) (hv.trans (le_max_left _ _))
    (hx.trans (le_max_left _ _)) (hy.trans (le_max_left _ _))
    (max_le hus hds) (max_le hvs hds) (max_le hxr hdr) (max_le hyr hdr)
    (le_max_right _ _) (le_max_right _ _) (le_max_right _ _) (le_max_right _ _)
  have hPbound :
      |geometricProduct θ (max x (d * r)) (max y (d * r)) -
        geometricProduct θ (max u (d * s)) (max v (d * s))| ≤ (2 / d) * ρ := by
    calc
      _ ≤ (1 / d) * (|max x (d * r) - max u (d * s)| +
          |max y (d * r) - max v (d * s)|) := hP
      _ ≤ (1 / d) * (ρ + ρ) :=
        mul_le_mul_of_nonneg_left (add_le_add hclipx hclipy) (by positivity)
      _ = (2 / d) * ρ := by ring
  apply (abs_max_sub_max_le_max _ _ _ _).trans
  apply max_le
  · exact hrs.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left (1:ℝ) (2 * A / d)) hρ)
  · rw [← mul_sub, abs_mul, abs_of_nonneg hA]
    calc
      _ ≤ A * ((2 / d) * ρ) := mul_le_mul_of_nonneg_left hPbound hA
      _ = (2 * A / d) * ρ := by ring
      _ ≤ max 1 (2 * A / d) * ρ := mul_le_mul_of_nonneg_right (le_max_right _ _) hρ

/-- The maximum regularization is globally Lipschitz for any three scalar size functions.
This covers the manuscript's pair norm and the two endpoint projection norms. -/
theorem maximum_regularization_lipschitz {E : Type*} [PseudoMetricSpace E]
    (r x y : E → ℝ) {A θ : ℝ} (hA : 1 ≤ A) (hθ : 0 < θ) (hθ' : θ < 1)
    (hr : LipschitzWith 1 r) (hx : LipschitzWith 1 x) (hy : LipschitzWith 1 y)
    (hx0 : ∀ z, 0 ≤ x z) (hy0 : ∀ z, 0 ≤ y z)
    (hxr : ∀ z, x z ≤ r z) (hyr : ∀ z, y z ≤ r z) :
    ∃ C : NNReal, LipschitzWith C (fun z => max (r z) (A * geometricProduct θ (x z) (y z))) := by
  obtain ⟨d, hd, hd1, hdx, hdy⟩ := exists_clipping_threshold hA hθ hθ'
  let C : NNReal := ⟨max 1 (2 * A / d), le_trans zero_le_one (le_max_left _ _)⟩
  refine ⟨C, LipschitzWith.of_dist_le_mul ?_⟩
  intro u v
  change |max (r u) (A * geometricProduct θ (x u) (y u)) -
    max (r v) (A * geometricProduct θ (x v) (y v))| ≤ max 1 (2 * A / d) * dist u v
  have hr' : |r u - r v| ≤ dist u v := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hr.dist_le_mul u v
  have hx' : |x u - x v| ≤ dist u v := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hx.dist_le_mul u v
  have hy' : |y u - y v| ≤ dist u v := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hy.dist_le_mul u v
  exact regularization_abs_difference_le (zero_le_one.trans hA) hθ.le hθ'.le hd hd1 hdx hdy
    ((hx0 u).trans (hxr u)) ((hx0 v).trans (hxr v)) (hx0 u) (hy0 u) (hx0 v) (hy0 v)
    (hxr u) (hyr u) (hxr v) (hyr v) dist_nonneg hr' hx' hy'

end BB
