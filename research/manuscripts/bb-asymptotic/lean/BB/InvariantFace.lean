import BB.Spectral
import BB.CoboundaryMeasure
import BB.FiniteRigidity
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Invariant averages for an actual fixed BB spectral face

The map obeys the genuine normalized BB update almost everywhere. The
endpoint potential is constructed from the actual endpoint weights; its
measurability and nonnegativity are proved. It is not assumed integrable.

The endpoint coordinates of both consecutive measures are positive almost
everywhere. This is an explicit fixed-face hypothesis. The file does not yet
construct the finite support partition of an arbitrary invariant measure, and
therefore does not by itself certify the paper's global invariant-measure
statement.

`Real.log 0` is used only to choose a finite measurable extension of the transfer
function outside the full-measure positive-endpoint set. All instances of the
spectral cohomology identity have genuinely positive endpoint weights and
positive norm multiplier.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace BB

variable {ι X : Type*} [Fintype ι] [MeasurableSpace X]

theorem simplex_coordinate_le_one {w : ι → ℝ} (hw : IsSimplex w) (i : ι) :
    w i ≤ 1 := by
  have hsum : w i ≤ ∑ j, w j :=
    Finset.single_le_sum (fun j _ => hw.1 j) (Finset.mem_univ i)
  simpa only [hw.2] using hsum

theorem endpointPotential_nonneg_on_simplex {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {w : ι → ℝ} (hw : IsSimplex w) (lo hi : ι) :
    0 ≤ endpointPotential a b (w lo) (w hi) := by
  obtain ⟨hp, hq⟩ := endpoint_weights_pos ha hab
  have hl : Real.log (w lo) ≤ 0 :=
    Real.log_nonpos (hw.1 lo) (simplex_coordinate_le_one hw lo)
  have hr : Real.log (w hi) ≤ 0 :=
    Real.log_nonpos (hw.1 hi) (simplex_coordinate_le_one hw hi)
  have hp2 : 0 ≤ leftWeight a b / 2 := div_nonneg hp.le (by norm_num)
  have hq2 : 0 ≤ rightWeight a b / 2 := div_nonneg hq.le (by norm_num)
  have hleft := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hp2) hl
  have hright := mul_nonpos_of_nonneg_of_nonpos hq2 hr
  unfold endpointPotential
  linarith

theorem endpointPotential_measurable (a b : ℝ) (w : X → ι → ℝ)
    (hw : ∀ i, Measurable (fun x => w x i)) (lo hi : ι) :
    Measurable (fun x => endpointPotential a b (w x lo) (w x hi)) := by
  exact (measurable_const.mul (hw lo).log).sub (measurable_const.mul (hw hi).log)

theorem spectral_mean_measurable (lam : ι → ℝ) (z : X → ι → ℝ)
    (hz : ∀ i, Measurable (fun x => z x i)) :
    Measurable (fun x => mean lam (z x)) :=
  Finset.measurable_sum _ (fun i _ => measurable_const.mul (hz i))

theorem endpointDefect_measurable (a b : ℝ) (lam : ι → ℝ) (z : X → ι → ℝ)
    (hz : ∀ i, Measurable (fun x => z x i)) :
    Measurable (fun x => endpointDefect a b (mean lam (z x))) := by
  have hm := spectral_mean_measurable lam z hz
  exact measurable_const.sub
    ((measurable_const.mul ((hm.sub measurable_const).div hm).log).add
      (measurable_const.mul ((measurable_const.sub hm).div hm).log))

/-- The actual zero-coordinate event is invariant modulo null sets under an
invariant measure of the BB update. No ergodicity or full-support hypothesis
is used. -/
theorem bb_zero_coordinate_persistent_ae
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (lam : ι → ℝ)
    (w z : X → ι → ℝ)
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (i : ι) : ∀ᵐ x ∂μ, w x i = 0 ↔ w (T x) i = 0 := by
  let A : Set X := {x | w x i = 0}
  have hA : MeasurableSet A := measurableSet_eq_fun (hwmeas i) measurable_const
  have hforward : A ≤ᵐ[μ] T ⁻¹' A := by
    filter_upwards [hupdate] with x hx
    intro hxA
    change w (T x) i = 0
    rw [hx]
    exact weight_update_zero hxA
  have hae : A =ᵐ[μ] T ⁻¹' A :=
    ae_eq_of_ae_subset_of_measure_ge hforward (hT.measure_preimage hA).le
      hA (measure_ne_top μ _)
  filter_upwards [hae] with x hx
  change (w x i = 0) = (w (T x) i = 0) at hx
  exact Iff.of_eq hx

/-- The two consecutive coordinates have the same zero pattern almost
everywhere for an invariant BB state distribution. -/
theorem bb_consecutive_supports_equal_ae
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (lam : ι → ℝ)
    (w z : X → ι → ℝ)
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x) :
    ∀ᵐ x ∂μ, ∀ i, w x i = 0 ↔ z x i = 0 := by
  apply ae_all_iff.mpr
  intro i
  have hzero := bb_zero_coordinate_persistent_ae μ T hT lam w z hwmeas hupdate i
  have hAtT : ∀ᵐ x ∂μ, w (T x) i = 0 ↔ z (T x) i = 0 := by
    filter_upwards [hzero, hshift] with x hx hxshift
    rw [hxshift]
    exact hx.symm
  have hwSet : MeasurableSet {x | w x i = 0} :=
    measurableSet_eq_fun (hwmeas i) measurable_const
  have hzSet : MeasurableSet {x | z x i = 0} :=
    measurableSet_eq_fun (hzmeas i) measurable_const
  have hp : MeasurableSet {x | w x i = 0 ↔ z x i = 0} :=
    (hwSet.mem.iff hzSet.mem).setOf
  have hmap : ∀ᵐ x ∂Measure.map T μ, w x i = 0 ↔ z x i = 0 :=
    (ae_map_iff hT.measurable.aemeasurable hp).mpr hAtT
  simpa only [hT.map_eq] using hmap

/-- Actual BB logarithmic growth on a positive-endpoint fixed face has
invariant average no larger than the endpoint constant. -/
theorem fixed_face_invariant_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hpositive : ∀ᵐ x ∂μ,
      0 < w x lo ∧ 0 < w x hi ∧ 0 < z x lo ∧ 0 < z x hi)
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ) :
    (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) ≤
      Real.log (rate a b) := by
  let H : X → ℝ := fun x => endpointPotential a b (w x lo) (w x hi)
  have hHmeas : Measurable H := endpointPotential_measurable a b w hwmeas lo hi
  have hHnonneg : ∀ x, 0 ≤ H x :=
    fun x => endpointPotential_nonneg_on_simplex ha hab (hw x) lo hi
  apply coboundary_integral_bound μ T hT H hHmeas hHnonneg _ hf (Real.log (rate a b))
  filter_upwards [hpositive, hupdate] with x hx hxupdate
  obtain ⟨hau, hub, _⟩ := endpoint_state_regular ha hab hlo hhi hlam
    (hw x) (hz x) hx.1 hx.2.2.1 hx.2.2.2
  have hdef := endpoint_defect_nonneg ha hau hub
  have hid := spectral_cohomology ha hab hlo hhi hlam (hw x) (hz x)
    hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
  rw [← hxupdate] at hid
  change Real.log (Real.sqrt (growthSq lam (w x) (z x))) ≤
    Real.log (rate a b) + endpointPotential a b (w (T x) lo) (w (T x) hi) -
      endpointPotential a b (w x lo) (w x hi)
  linarith

/-- Equality of the fixed-face invariant average forces the delayed spectral
mean to equal the midpoint almost everywhere. -/
theorem fixed_face_midpoint_of_maximal_integral
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hpositive : ∀ᵐ x ∂μ,
      0 < w x lo ∧ 0 < w x hi ∧ 0 < z x lo ∧ 0 < z x hi)
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ)
    (hmaximal : (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) =
      Real.log (rate a b)) :
    ∀ᵐ x ∂μ, mean lam (z x) = (a + b) / 2 := by
  let H : X → ℝ := fun x => endpointPotential a b (w x lo) (w x hi)
  let D : X → ℝ := fun x => max (endpointDefect a b (mean lam (z x))) 0
  have hHmeas : Measurable H := endpointPotential_measurable a b w hwmeas lo hi
  have hHnonneg : ∀ x, 0 ≤ H x :=
    fun x => endpointPotential_nonneg_on_simplex ha hab (hw x) lo hi
  have hDmeas : Measurable D :=
    (endpointDefect_measurable a b lam z hzmeas).max measurable_const
  have hDnonneg : ∀ x, 0 ≤ D x := fun x => le_max_right _ _
  have hineq : ∀ᵐ x ∂μ,
      Real.log (Real.sqrt (growthSq lam (w x) (z x))) + D x ≤
        Real.log (rate a b) + H (T x) - H x := by
    filter_upwards [hpositive, hupdate] with x hx hxupdate
    obtain ⟨hau, hub, _⟩ := endpoint_state_regular ha hab hlo hhi hlam
      (hw x) (hz x) hx.1 hx.2.2.1 hx.2.2.2
    have hdef := endpoint_defect_nonneg ha hau hub
    have hid := spectral_cohomology ha hab hlo hhi hlam (hw x) (hz x)
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
    rw [← hxupdate] at hid
    change Real.log (Real.sqrt (growthSq lam (w x) (z x))) +
      max (endpointDefect a b (mean lam (z x))) 0 ≤
        Real.log (rate a b) + endpointPotential a b (w (T x) lo) (w (T x) hi) -
          endpointPotential a b (w x lo) (w x hi)
    rw [max_eq_left hdef]
    linarith
  have hDzero := coboundary_defect_zero_of_maximal_integral μ T hT H hHmeas hHnonneg
    _ hf (Real.log (rate a b)) D hDmeas hDnonneg hineq hmaximal
  filter_upwards [hpositive, hDzero] with x hx hxD
  obtain ⟨hau, hub, _⟩ := endpoint_state_regular ha hab hlo hhi hlam
    (hw x) (hz x) hx.1 hx.2.2.1 hx.2.2.2
  apply (endpoint_defect_eq_zero_iff ha hau hub).mp
  have hdef := endpoint_defect_nonneg ha hau hub
  simpa only [D, max_eq_left hdef] using hxD

theorem log_integral_rigidity
    (μ : Measure X) [IsProbabilityMeasure μ] (r : X → ℝ) (c : ℝ)
    (hc : 0 < c) (hr : ∀ᵐ x ∂μ, 0 < r x) (hle : ∀ᵐ x ∂μ, r x ≤ c)
    (hf : Integrable (fun x => Real.log (r x)) μ)
    (heq : (∫ x, Real.log (r x) ∂μ) = Real.log c) :
    ∀ᵐ x ∂μ, r x = c := by
  have hlogle : (fun x => Real.log (r x)) ≤ᵐ[μ] (fun _ => Real.log c) := by
    filter_upwards [hr, hle] with x hx hxc
    exact Real.log_le_log hx hxc
  have hint : (∫ x, Real.log (r x) ∂μ) = ∫ _ : X, Real.log c ∂μ := by
    simpa only [integral_const, measure_univ, ENNReal.one_toReal, one_smul] using heq
  have hae := (integral_eq_iff_of_ae_le hf (integrable_const (Real.log c)) hlogle).mp hint
  filter_upwards [hae, hr] with x hx hxr
  exact Real.log_injOn_pos (Set.mem_Ioi.mpr hxr) (Set.mem_Ioi.mpr hc) hx

theorem fixed_face_growth_eq_of_maximal_integral
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hpositive : ∀ᵐ x ∂μ,
      0 < w x lo ∧ 0 < w x hi ∧ 0 < z x lo ∧ 0 < z x hi)
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ)
    (hmaximal : (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) =
      Real.log (rate a b)) :
    ∀ᵐ x ∂μ, growthSq lam (w x) (z x) = (rate a b) ^ 2 := by
  have hmean := fixed_face_midpoint_of_maximal_integral μ T hT lam lo hi a b
    ha hab hlo hhi hlam w z hw hz hwmeas hzmeas hpositive hupdate hf hmaximal
  have hr : ∀ᵐ x ∂μ, 0 < Real.sqrt (growthSq lam (w x) (z x)) := by
    filter_upwards [hpositive] with x hx
    exact Real.sqrt_pos.mpr (endpoint_state_regular ha hab hlo hhi hlam (hw x) (hz x)
      hx.1 hx.2.2.1 hx.2.2.2).2.2
  have hle : ∀ᵐ x ∂μ, Real.sqrt (growthSq lam (w x) (z x)) ≤ rate a b := by
    filter_upwards [hmean] with x hx
    exact (Real.sqrt_le_left (rate_pos ha hab).le).mpr
      (growth_sq_midpoint_le lam (w x) (z x) a b ha hab hlam (hw x) hx)
  have hroot := log_integral_rigidity μ _ (rate a b) (rate_pos ha hab) hr hle hf hmaximal
  filter_upwards [hroot] with x hx
  calc
    growthSq lam (w x) (z x) = (Real.sqrt (growthSq lam (w x) (z x))) ^ 2 :=
      (Real.sq_sqrt (growth_sq_nonneg (hw x))).symm
    _ = (rate a b) ^ 2 := by rw [hx]

/-- Every maximal state in the fixed-face invariant distribution is the
balanced two-endpoint state. Injectivity of `lam` encodes distinct spectral
values; multiplicities have already been combined into eigenspace weights. -/
theorem fixed_face_maximal_state
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (hinj : Function.Injective lam) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hpositive : ∀ᵐ x ∂μ,
      0 < w x lo ∧ 0 < w x hi ∧ 0 < z x lo ∧ 0 < z x hi)
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x)
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ)
    (hmaximal : (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) =
      Real.log (rate a b)) :
    ∀ᵐ x ∂μ, (w x lo = 1 / 2 ∧ w x hi = 1 / 2) ∧
      (z x lo = 1 / 2 ∧ z x hi = 1 / 2) ∧
      (∀ i, i ≠ lo → i ≠ hi → w x i = 0 ∧ z x i = 0) := by
  have hmean := fixed_face_midpoint_of_maximal_integral μ T hT lam lo hi a b
    ha hab hlo hhi hlam w z hw hz hwmeas hzmeas hpositive hupdate hf hmaximal
  have hgrowth := fixed_face_growth_eq_of_maximal_integral μ T hT lam lo hi a b
    ha hab hlo hhi hlam w z hw hz hwmeas hzmeas hpositive hupdate hf hmaximal
  have hsupport := bb_consecutive_supports_equal_ae μ T hT lam w z
    hwmeas hzmeas hupdate hshift
  have hmeanT := hT.quasiMeasurePreserving.ae hmean
  filter_upwards [hmean, hgrowth, hsupport, hmeanT, hshift] with x hxmean hxgrowth hxsp hxmeanT hxshift
  have hmeanw : mean lam (w x) = (a + b) / 2 := by simpa only [hxshift] using hxmeanT
  have hactive := (growth_sq_midpoint_eq_iff lam (w x) (z x) a b ha hab hlam (hw x) hxmean).mp hxgrowth
  have hzeroW : ∀ i, i ≠ lo → i ≠ hi → w x i = 0 := by
    intro i hnlo hnhi
    by_contra hnzero
    rcases hactive i hnzero with hia | hib
    · exact hnlo (hinj (hia.trans hlo.symm))
    · exact hnhi (hinj (hib.trans hhi.symm))
  have hzeroZ : ∀ i, i ≠ lo → i ≠ hi → z x i = 0 := by
    intro i hnlo hnhi
    exact (hxsp i).mp (hzeroW i hnlo hnhi)
  exact ⟨endpoint_balance_of_simplex_mean lam (w x) lo hi a b hab hlo hhi (hw x) hmeanw hzeroW,
    endpoint_balance_of_simplex_mean lam (z x) lo hi a b hab hlo hhi (hz x) hxmean hzeroZ,
    fun i hnlo hnhi => ⟨hzeroW i hnlo hnhi, hzeroZ i hnlo hnhi⟩⟩

end BB
