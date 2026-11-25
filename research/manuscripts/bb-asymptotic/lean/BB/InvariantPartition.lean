import BB.InvariantFace
import Mathlib.MeasureTheory.Integral.SetIntegral

/-!
# Finite invariant support partitions

This file handles arbitrary finite BB supports.  The endpoint transfer
functions are selected on each support class and glued into one finite,
measurable, nonnegative function.  The invariant-average argument therefore
does not require ergodic decomposition or an integrable transfer function.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped BigOperators

namespace BB

variable {X : Type*} [MeasurableSpace X]

/-- Restriction to an event that is invariant modulo null sets preserves
measure preservation; the event need not have positive mass. -/
theorem measurePreserving_restrict_invariant
    (μ : Measure X) (T : X → X) (hT : MeasurePreserving T μ μ)
    (A : Set X) (hA : MeasurableSet A) (hInv : A =ᵐ[μ] T ⁻¹' A) :
    MeasurePreserving T (μ.restrict A) (μ.restrict A) := by
  have hres := hT.restrict_preimage hA
  rwa [← Measure.restrict_congr_set hInv] at hres

/-- Finite-measure form of the unbounded-transfer estimate, useful on
unnormalized restrictions to support classes. -/
theorem coboundary_integral_bound_finite
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (h : X → ℝ) (hh : Measurable h) (hnonneg : ∀ x, 0 ≤ h x)
    (f : X → ℝ) (hf : Integrable f μ) (β : ℝ)
    (hbound : ∀ᵐ x ∂μ, f x ≤ β + h (T x) - h x) :
    (∫ x, f x ∂μ) ≤ (μ univ).toReal * β := by
  have hshift : ∀ᵐ x ∂μ, f x - β ≤ h (T x) - h x := by
    filter_upwards [hbound] with x hx
    linarith
  have hle := integral_le_zero_of_le_coboundary μ T hT h hh hnonneg
    (fun x => f x - β) (hf.sub (integrable_const β)) hshift
  rw [integral_sub hf (integrable_const β)] at hle
  simpa only [integral_const, smul_eq_mul, sub_nonpos] using hle

/-- Exact averaging over a finite measurable partition. -/
theorem integral_finite_partition {κ : Type*} [Fintype κ]
    (μ : Measure X) (A : κ → Set X)
    (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (Disjoint on A)) (hcover : (⋃ i, A i) = univ)
    (f : X → ℝ) (hf : Integrable f μ) :
    (∫ x, f x ∂μ) = ∑ i, ∫ x in A i, f x ∂μ := by
  have h := integral_fintype_iUnion hA hdisjoint
    (fun i => hf.mono_measure Measure.restrict_le_self)
  simpa only [hcover, integral_univ] using h

/-- Gluing nonnegative transfer functions on an invariant finite partition.
The component inequalities may hold only almost everywhere on their classes.
No component transfer function is assumed integrable. -/
theorem finite_partition_coboundary_bound {κ : Type*} [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (A : κ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (Disjoint on A))
    (hcover : ∀ x, ∃ i, x ∈ A i)
    (hInv : ∀ i, ∀ᵐ x ∂μ, x ∈ A i ↔ T x ∈ A i)
    (f : X → ℝ) (hf : Integrable f μ) (β : ℝ)
    (H : κ → X → ℝ) (hH : ∀ i, Measurable (H i))
    (hHnonneg : ∀ i x, 0 ≤ H i x)
    (hbound : ∀ i, ∀ᵐ x ∂μ,
      x ∈ A i → f x ≤ β + H i (T x) - H i x) :
    (∫ x, f x ∂μ) ≤ β := by
  classical
  let G : X → ℝ := fun x => ∑ i, (A i).indicator (H i) x
  have hG : Measurable G := Finset.measurable_sum _
    (fun i _ => (hH i).indicator (hA i))
  have hGnonneg : ∀ x, 0 ≤ G x := by
    intro x
    exact Finset.sum_nonneg (fun i _ => indicator_nonneg (fun y _ => hHnonneg i y) x)
  have hGclass : ∀ i x, x ∈ A i → G x = H i x := by
    intro i x hx
    dsimp only [G]
    rw [Finset.sum_eq_single i]
    · exact indicator_of_mem hx _
    · intro j _ hji
      apply indicator_of_not_mem
      intro hxj
      exact Set.disjoint_left.mp (hdisjoint hji) hxj hx
    · simp
  apply coboundary_integral_bound μ T hT G hG hGnonneg f hf β
  have hInvAll := ae_all_iff.mpr hInv
  have hboundAll := ae_all_iff.mpr hbound
  filter_upwards [hInvAll, hboundAll] with x hxInv hxBound
  obtain ⟨i, hxi⟩ := hcover x
  rw [hGclass i x hxi, hGclass i (T x) ((hxInv i).mp hxi)]
  exact hxBound i hxi

/-- A sum of indicators of a disjoint family selects its unique occupied
component. -/
theorem disjoint_indicator_sum_eq {κ : Type*} [Fintype κ]
    (A : κ → Set X) (hdisjoint : Pairwise (Disjoint on A))
    (F : κ → X → ℝ) (i : κ) (x : X) (hx : x ∈ A i) :
    (∑ j, (A j).indicator (F j) x) = F i x := by
  classical
  rw [Finset.sum_eq_single i]
  · exact indicator_of_mem hx _
  · intro j _ hji
    apply indicator_of_not_mem
    intro hxj
    exact Set.disjoint_left.mp (hdisjoint hji) hxj hx
  · simp

/-- A maximal invariant average gives full mass to components with the
maximal component bound. The deficit is a bounded function because the
partition is finite; the transfer functions can remain unbounded. -/
theorem finite_partition_rates_of_maximal_integral {κ : Type*} [Fintype κ]
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (A : κ → Set X) (hA : ∀ i, MeasurableSet (A i))
    (hdisjoint : Pairwise (Disjoint on A))
    (hcover : ∀ x, ∃ i, x ∈ A i)
    (hInv : ∀ i, ∀ᵐ x ∂μ, x ∈ A i ↔ T x ∈ A i)
    (f : X → ℝ) (hf : Integrable f μ) (β : ℝ)
    (βi : κ → ℝ) (hβi : ∀ i, βi i ≤ β)
    (H : κ → X → ℝ) (hH : ∀ i, Measurable (H i))
    (hHnonneg : ∀ i x, 0 ≤ H i x)
    (hbound : ∀ i, ∀ᵐ x ∂μ,
      x ∈ A i → f x ≤ βi i + H i (T x) - H i x)
    (hmaximal : (∫ x, f x ∂μ) = β) :
    ∀ᵐ x ∂μ, ∀ i, x ∈ A i → βi i = β := by
  classical
  let G : X → ℝ := fun x => ∑ i, (A i).indicator (H i) x
  let D : X → ℝ := fun x => ∑ i, (A i).indicator (fun _ => β - βi i) x
  have hG : Measurable G := Finset.measurable_sum _
    (fun i _ => (hH i).indicator (hA i))
  have hD : Measurable D := Finset.measurable_sum _
    (fun i _ => measurable_const.indicator (hA i))
  have hGnonneg : ∀ x, 0 ≤ G x := fun x =>
    Finset.sum_nonneg (fun i _ => indicator_nonneg (fun y _ => hHnonneg i y) x)
  have hDnonneg : ∀ x, 0 ≤ D x := fun x =>
    Finset.sum_nonneg (fun i _ =>
      indicator_nonneg (fun _ _ => sub_nonneg.mpr (hβi i)) x)
  have hGclass : ∀ i x, x ∈ A i → G x = H i x :=
    disjoint_indicator_sum_eq A hdisjoint H
  have hDclass : ∀ i x, x ∈ A i → D x = β - βi i :=
    disjoint_indicator_sum_eq A hdisjoint (fun i _ => β - βi i)
  have hineq : ∀ᵐ x ∂μ, f x + D x ≤ β + G (T x) - G x := by
    have hInvAll := ae_all_iff.mpr hInv
    have hboundAll := ae_all_iff.mpr hbound
    filter_upwards [hInvAll, hboundAll] with x hxInv hxBound
    obtain ⟨i, hxi⟩ := hcover x
    rw [hDclass i x hxi, hGclass i x hxi, hGclass i (T x) ((hxInv i).mp hxi)]
    have hi := hxBound i hxi
    linarith
  have hzero := coboundary_defect_zero_of_maximal_integral μ T hT G hG hGnonneg
    f hf β D hD hDnonneg hineq hmaximal
  filter_upwards [hzero] with x hx i hxi
  rw [hDclass i x hxi] at hx
  exact (sub_eq_zero.mp hx).symm

/-- Equality in interval monotonicity forces equality of both positive
spectral endpoints. -/
theorem rate_eq_of_nested_iff {a b A B : ℝ}
    (hA : 0 < A) (hAa : A ≤ a) (hab : a < b) (hbB : b ≤ B) :
    rate a b = rate A B ↔ a = A ∧ b = B := by
  have ha : 0 < a := hA.trans_le hAa
  have hb : 0 < b := ha.trans hab
  have hB : 0 < B := hb.trans_le hbB
  have hs : b + a ≠ 0 := ne_of_gt (add_pos hb ha)
  have hS : B + A ≠ 0 := ne_of_gt (add_pos hB hA)
  constructor
  · intro heq
    have hcross := (div_eq_div_iff hs hS).mp heq
    have hleft : B * (a - A) = 0 := by
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hAa),
        mul_nonneg hA.le (sub_nonneg.mpr hbB)]
    have hright : A * (B - b) = 0 := by
      nlinarith [mul_nonneg hB.le (sub_nonneg.mpr hAa),
        mul_nonneg hA.le (sub_nonneg.mpr hbB)]
    exact ⟨sub_eq_zero.mp ((mul_eq_zero.mp hleft).resolve_left (ne_of_gt hB)),
      (sub_eq_zero.mp ((mul_eq_zero.mp hright).resolve_left (ne_of_gt hA))).symm⟩
  · rintro ⟨rfl, rfl⟩
    rfl

variable {ι : Type*} [Fintype ι]

/-- The class with precisely the nonzero coordinates indexed by `J`. -/
def supportClass (w : X → ι → ℝ) (J : Finset ι) : Set X :=
  {x | ∀ i, w x i ≠ 0 ↔ i ∈ J}

theorem supportClass_measurable (w : X → ι → ℝ)
    (hw : ∀ i, Measurable (fun x => w x i)) (J : Finset ι) :
    MeasurableSet (supportClass w J) := by
  classical
  simp only [supportClass, setOf_forall]
  apply MeasurableSet.iInter
  intro i
  change MeasurableSet {x | w x i ≠ 0 ↔ i ∈ J}
  by_cases hi : i ∈ J
  · simpa only [hi, iff_true] using (measurableSet_eq_fun (hw i) measurable_const).compl
  · simpa only [hi, iff_false, not_not] using measurableSet_eq_fun (hw i) measurable_const

theorem supportClass_disjoint (w : X → ι → ℝ) :
    Pairwise (Disjoint on supportClass w) := by
  classical
  intro J K hJK
  apply Set.disjoint_left.mpr
  intro x hxJ hxK
  apply hJK
  ext i
  exact (hxJ i).symm.trans (hxK i)

theorem supportClass_cover (w : X → ι → ℝ) (x : X) :
    ∃ J, x ∈ supportClass w J := by
  classical
  refine ⟨Finset.univ.filter (fun i => w x i ≠ 0), ?_⟩
  intro i
  simp

/-- Every finite support class is invariant modulo null sets for the actual
BB update. -/
theorem supportClass_invariant_ae
    (μ : Measure X) [IsFiniteMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ) (lam : ι → ℝ)
    (w z : X → ι → ℝ)
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (J : Finset ι) :
    ∀ᵐ x ∂μ, x ∈ supportClass w J ↔ T x ∈ supportClass w J := by
  have hall := ae_all_iff.mpr
    (bb_zero_coordinate_persistent_ae μ T hT lam w z hwmeas hupdate)
  filter_upwards [hall] with x hx
  constructor
  · intro hxi i
    exact (not_congr (hx i)).symm.trans (hxi i)
  · intro hxi i
    exact (not_congr (hx i)).trans (hxi i)

/-- The cohomology identity depends only on the two endpoint values, the
interior mean and positive growth. Unused coordinates may lie outside the
local support interval. -/
theorem spectral_cohomology_of_interior_mean
    {lam w z : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hlo : lam lo = a) (hhi : lam hi = b)
    (hau : a < mean lam z) (hub : mean lam z < b)
    (hwlo : 0 < w lo) (hwhi : 0 < w hi)
    (hR : 0 < growthSq lam w z) :
    Real.log (Real.sqrt (growthSq lam w z)) =
      Real.log (rate a b) - endpointDefect a b (mean lam z) +
        endpointPotential a b (weightUpdate lam w z lo) (weightUpdate lam w z hi) -
          endpointPotential a b (w lo) (w hi) := by
  have hu : mean lam z ≠ 0 := ne_of_gt (lt_trans ha hau)
  have h1 : (1 - a / mean lam z)^2 = ((mean lam z - a) / mean lam z)^2 := by
    congr 1
    field_simp
  have h2 : (1 - b / mean lam z)^2 = ((b - mean lam z) / mean lam z)^2 := by
    field_simp
    ring
  rw [Real.log_sqrt hR.le]
  unfold weightUpdate multiplier
  rw [hlo, hhi, h1, h2]
  exact endpoint_cohomology ha hau hub hwlo hwhi hR

/-- Lower bound using only the active coordinates. -/
theorem mean_strict_lower_on_support {lam w : ι → ℝ} {a : ℝ} {j : ι}
    (hw : IsSimplex w) (hlam : ∀ i, w i ≠ 0 → a ≤ lam i)
    (hj : a < lam j) (hwj : 0 < w j) : a < mean lam w := by
  have hterm : ∀ i, 0 ≤ (lam i - a) * w i := by
    intro i
    by_cases hi : w i = 0
    · simp only [hi, mul_zero, le_refl]
    · exact mul_nonneg (sub_nonneg.mpr (hlam i hi)) (hw.1 i)
  have hsum : 0 < ∑ i, (lam i - a) * w i :=
    Finset.sum_pos' (fun i _ => hterm i)
      ⟨j, Finset.mem_univ j, mul_pos (sub_pos.mpr hj) hwj⟩
  have hid : (∑ i, (lam i - a) * w i) = mean lam w - a := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2, mul_one]
    rfl
  rw [hid] at hsum
  linarith

theorem mean_strict_upper_on_support {lam w : ι → ℝ} {b : ℝ} {j : ι}
    (hw : IsSimplex w) (hlam : ∀ i, w i ≠ 0 → lam i ≤ b)
    (hj : lam j < b) (hwj : 0 < w j) : mean lam w < b := by
  have hterm : ∀ i, 0 ≤ (b - lam i) * w i := by
    intro i
    by_cases hi : w i = 0
    · simp only [hi, mul_zero, le_refl]
    · exact mul_nonneg (sub_nonneg.mpr (hlam i hi)) (hw.1 i)
  have hsum : 0 < ∑ i, (b - lam i) * w i :=
    Finset.sum_pos' (fun i _ => hterm i)
      ⟨j, Finset.mem_univ j, mul_pos (sub_pos.mpr hj) hwj⟩
  have hid : (∑ i, (b - lam i) * w i) = b - mean lam w := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hw.2, mul_one]
    rfl
  rw [hid] at hsum
  linarith

theorem mean_eq_of_constant_on_support {lam w : ι → ℝ} {a : ℝ}
    (hw : IsSimplex w) (hlam : ∀ i, w i ≠ 0 → lam i = a) :
    mean lam w = a := by
  calc
    mean lam w = ∑ i, a * w i := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : w i = 0
      · simp only [hi, mul_zero]
      · rw [hlam i hi]
    _ = a := by rw [← Finset.mul_sum, hw.2, mul_one]

/-- A regular pair with a common finite support has distinct active spectral
endpoints. Repeated eigenvalue labels are allowed. -/
theorem regular_support_endpoints
    (lam w z : ι → ℝ) (J : Finset ι)
    (hlam : ∀ i, 0 < lam i) (hw : IsSimplex w) (hz : IsSimplex z)
    (hwsupp : ∀ i, w i ≠ 0 ↔ i ∈ J)
    (hzsupp : ∀ i, z i ≠ 0 ↔ i ∈ J)
    (hR : 0 < growthSq lam w z) :
    ∃ lo ∈ J, ∃ hi ∈ J, lam lo < lam hi ∧
      ∀ i ∈ J, lam lo ≤ lam i ∧ lam i ≤ lam hi := by
  classical
  have hactive : ∃ i, w i ≠ 0 := by
    by_contra h
    push_neg at h
    have hsum := hw.2
    simp only [h, Finset.sum_const_zero, zero_ne_one] at hsum
  obtain ⟨i, hi⟩ := hactive
  have hJ : J.Nonempty := ⟨i, (hwsupp i).mp hi⟩
  obtain ⟨lo, hlo, hmin⟩ := J.exists_min_image lam hJ
  obtain ⟨hi, hhi, hmax⟩ := J.exists_max_image lam hJ
  refine ⟨lo, hlo, hi, hhi, ?_, fun j hj => ⟨hmin j hj, hmax j hj⟩⟩
  by_contra hlt
  have heq : lam hi = lam lo := le_antisymm (le_of_not_gt hlt) (hmin hi hhi)
  have hconstant : ∀ j ∈ J, lam j = lam lo := by
    intro j hj
    exact le_antisymm (by simpa only [heq] using hmax j hj) (hmin j hj)
  have hmean : mean lam z = lam lo := mean_eq_of_constant_on_support hz
    (fun j hj => hconstant j ((hzsupp j).mp hj))
  have hzero : growthSq lam w z = 0 := by
    unfold growthSq
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : w j = 0
    · simp only [hj, mul_zero]
    · have hlamj := hconstant j ((hwsupp j).mp hj)
      simp only [multiplier, hmean, hlamj, div_self (ne_of_gt (hlam lo)),
        sub_self, zero_pow (by decide : 2 ≠ 0), zero_mul]
  linarith

/-- The full finite-dimensional invariant-average bound on arbitrary
supports.  The state observables follow the actual BB update and delayed
shift almost everywhere, and the measure gives full mass to nonterminal
states.  Endpoint masses, ergodicity and support constancy are not assumed.

Repeated spectral labels are allowed: injectivity is unnecessary for this
inequality.  Integrability is the finite-valued branch of the logarithmic
observable; the extended-integral `-∞` branch is a separate convention.
-/
theorem finite_spectral_invariant_bound
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (a b : ℝ) (ha : 0 < a)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hregular : ∀ᵐ x ∂μ, 0 < growthSq lam (w x) (z x))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x)
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ) :
    (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) ≤
      Real.log (rate a b) := by
  classical
  have hpositive : ∀ i, 0 < lam i := fun i => ha.trans_le (hlam i).1
  have hcommon := bb_consecutive_supports_equal_ae μ T hT lam w z
    hwmeas hzmeas hupdate hshift
  have hpotentials : ∀ J : Finset ι, ∃ H : X → ℝ,
      Measurable H ∧ (∀ x, 0 ≤ H x) ∧
      ∀ᵐ x ∂μ, x ∈ supportClass w J →
        Real.log (Real.sqrt (growthSq lam (w x) (z x))) ≤
          Real.log (rate a b) + H (T x) - H x := by
    intro J
    by_cases hrealized : ∃ x, x ∈ supportClass w J ∧
        (∀ i, w x i = 0 ↔ z x i = 0) ∧ 0 < growthSq lam (w x) (z x)
    · obtain ⟨x₀, hx₀J, hx₀common, hx₀regular⟩ := hrealized
      have hz₀J : ∀ i, z x₀ i ≠ 0 ↔ i ∈ J := fun i =>
        (not_congr (hx₀common i)).symm.trans (hx₀J i)
      obtain ⟨lo, hloJ, hi, hhiJ, hab, hbounds⟩ :=
        regular_support_endpoints lam (w x₀) (z x₀) J hpositive
          (hw x₀) (hz x₀) hx₀J hz₀J hx₀regular
      let H : X → ℝ := fun x =>
        endpointPotential (lam lo) (lam hi) (w x lo) (w x hi)
      refine ⟨H, endpointPotential_measurable _ _ w hwmeas lo hi,
        fun x => endpointPotential_nonneg_on_simplex (hpositive lo) hab (hw x) lo hi, ?_⟩
      filter_upwards [hcommon, hregular, hupdate] with x hxcommon hxregular hxupdate
      intro hxJ
      have hzJ : ∀ i, z x i ≠ 0 ↔ i ∈ J := fun i =>
        (not_congr (hxcommon i)).symm.trans (hxJ i)
      have hwlo : 0 < w x lo :=
        lt_of_le_of_ne ((hw x).1 lo) (Ne.symm ((hxJ lo).mpr hloJ))
      have hwhi : 0 < w x hi := by
        exact lt_of_le_of_ne ((hw x).1 hi) (Ne.symm ((hxJ hi).mpr hhiJ))
      have hzlo : 0 < z x lo := by
        exact lt_of_le_of_ne ((hz x).1 lo) (Ne.symm ((hzJ lo).mpr hloJ))
      have hzhi : 0 < z x hi := by
        exact lt_of_le_of_ne ((hz x).1 hi) (Ne.symm ((hzJ hi).mpr hhiJ))
      have hau : lam lo < mean lam (z x) :=
        mean_strict_lower_on_support (hz x)
          (fun i hi => (hbounds i ((hzJ i).mp hi)).1) hab hzhi
      have hub : mean lam (z x) < lam hi :=
        mean_strict_upper_on_support (hz x)
          (fun i hi => (hbounds i ((hzJ i).mp hi)).2) hab hzlo
      have hdef := endpoint_defect_nonneg (hpositive lo) hau hub
      have hid := spectral_cohomology_of_interior_mean (hpositive lo)
        (rfl : lam lo = lam lo) (rfl : lam hi = lam hi)
        hau hub hwlo hwhi hxregular
      rw [← hxupdate] at hid
      have hlog : Real.log (rate (lam lo) (lam hi)) ≤ Real.log (rate a b) :=
        Real.log_le_log (rate_pos (hpositive lo) hab)
          (rate_mono_interval ha (hlam lo).1 hab.le (hlam hi).2)
      change Real.log (Real.sqrt (growthSq lam (w x) (z x))) ≤
        Real.log (rate a b) +
          endpointPotential (lam lo) (lam hi) (w (T x) lo) (w (T x) hi) -
          endpointPotential (lam lo) (lam hi) (w x lo) (w x hi)
      linarith
    · refine ⟨fun _ => 0, measurable_const, fun _ => le_rfl, ?_⟩
      filter_upwards [hcommon, hregular] with x hxcommon hxregular
      intro hxJ
      exact (hrealized ⟨x, hxJ, hxcommon, hxregular⟩).elim
  choose H hH hHnonneg hbound using hpotentials
  exact finite_partition_coboundary_bound μ T hT (supportClass w)
    (supportClass_measurable w hwmeas) (supportClass_disjoint w) (supportClass_cover w)
    (supportClass_invariant_ae μ T hT lam w z hwmeas hupdate)
    _ hf (Real.log (rate a b)) H hH hHnonneg hbound

/-- The exact local endpoint certificate on one arbitrary active support. -/
theorem spectral_support_class_transfer
    (μ : Measure X) (T : X → X) (lam : ι → ℝ)
    (J : Finset ι) (lo hi : ι)
    (hpositive : ∀ i, 0 < lam i) (hloJ : lo ∈ J) (hhiJ : hi ∈ J)
    (hab : lam lo < lam hi)
    (hbounds : ∀ i ∈ J, lam lo ≤ lam i ∧ lam i ≤ lam hi)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hcommon : ∀ᵐ x ∂μ, ∀ i, w x i = 0 ↔ z x i = 0)
    (hregular : ∀ᵐ x ∂μ, 0 < growthSq lam (w x) (z x))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x)) :
    ∀ᵐ x ∂μ, x ∈ supportClass w J →
      Real.log (Real.sqrt (growthSq lam (w x) (z x))) ≤
        Real.log (rate (lam lo) (lam hi)) +
          endpointPotential (lam lo) (lam hi) (w (T x) lo) (w (T x) hi) -
          endpointPotential (lam lo) (lam hi) (w x lo) (w x hi) := by
  filter_upwards [hcommon, hregular, hupdate] with x hxcommon hxregular hxupdate
  intro hxJ
  have hzJ : ∀ i, z x i ≠ 0 ↔ i ∈ J := fun i =>
    (not_congr (hxcommon i)).symm.trans (hxJ i)
  have hwlo : 0 < w x lo :=
    lt_of_le_of_ne ((hw x).1 lo) (Ne.symm ((hxJ lo).mpr hloJ))
  have hwhi : 0 < w x hi :=
    lt_of_le_of_ne ((hw x).1 hi) (Ne.symm ((hxJ hi).mpr hhiJ))
  have hzlo : 0 < z x lo :=
    lt_of_le_of_ne ((hz x).1 lo) (Ne.symm ((hzJ lo).mpr hloJ))
  have hzhi : 0 < z x hi :=
    lt_of_le_of_ne ((hz x).1 hi) (Ne.symm ((hzJ hi).mpr hhiJ))
  have hau : lam lo < mean lam (z x) := mean_strict_lower_on_support (hz x)
    (fun i hi => (hbounds i ((hzJ i).mp hi)).1) hab hzhi
  have hub : mean lam (z x) < lam hi := mean_strict_upper_on_support (hz x)
    (fun i hi => (hbounds i ((hzJ i).mp hi)).2) hab hzlo
  have hdef := endpoint_defect_nonneg (hpositive lo) hau hub
  have hid := spectral_cohomology_of_interior_mean (hpositive lo)
    (rfl : lam lo = lam lo) (rfl : lam hi = lam hi) hau hub hwlo hwhi hxregular
  rw [← hxupdate] at hid
  linarith

/-- Maximal invariant average forces positive mass at both global spectral
endpoints. This conclusion is derived from the finite support partition. -/
theorem finite_spectral_endpoint_mass_of_maximal_integral
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (hinj : Function.Injective lam) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hregular : ∀ᵐ x ∂μ, 0 < growthSq lam (w x) (z x))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x)
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ)
    (hmaximal : (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) =
      Real.log (rate a b)) :
    ∀ᵐ x ∂μ, 0 < w x lo ∧ 0 < w x hi ∧ 0 < z x lo ∧ 0 < z x hi := by
  classical
  have hpositive : ∀ i, 0 < lam i := fun i => ha.trans_le (hlam i).1
  have hcommon := bb_consecutive_supports_equal_ae μ T hT lam w z
    hwmeas hzmeas hupdate hshift
  have hcertificates : ∀ J : Finset ι, ∃ βJ : ℝ, ∃ H : X → ℝ,
      Measurable H ∧ (∀ x, 0 ≤ H x) ∧ βJ ≤ Real.log (rate a b) ∧
      (∀ᵐ x ∂μ, x ∈ supportClass w J →
        Real.log (Real.sqrt (growthSq lam (w x) (z x))) ≤ βJ + H (T x) - H x) ∧
      (∀ᵐ x ∂μ, βJ = Real.log (rate a b) → x ∈ supportClass w J →
        0 < w x lo ∧ 0 < w x hi) := by
    intro J
    by_cases hrealized : ∃ x, x ∈ supportClass w J ∧
        (∀ i, w x i = 0 ↔ z x i = 0) ∧ 0 < growthSq lam (w x) (z x)
    · obtain ⟨x₀, hx₀J, hx₀common, hx₀regular⟩ := hrealized
      have hz₀J : ∀ i, z x₀ i ≠ 0 ↔ i ∈ J := fun i =>
        (not_congr (hx₀common i)).symm.trans (hx₀J i)
      obtain ⟨iL, hiLJ, iU, hiUJ, hLU, hbounds⟩ :=
        regular_support_endpoints lam (w x₀) (z x₀) J hpositive
          (hw x₀) (hz x₀) hx₀J hz₀J hx₀regular
      let H : X → ℝ := fun x =>
        endpointPotential (lam iL) (lam iU) (w x iL) (w x iU)
      refine ⟨Real.log (rate (lam iL) (lam iU)), H,
        endpointPotential_measurable _ _ w hwmeas iL iU,
        fun x => endpointPotential_nonneg_on_simplex (hpositive iL) hLU (hw x) iL iU,
        ?_, ?_, ?_⟩
      · exact Real.log_le_log (rate_pos (hpositive iL) hLU)
          (rate_mono_interval ha (hlam iL).1 hLU.le (hlam iU).2)
      · exact spectral_support_class_transfer μ T lam J iL iU hpositive hiLJ hiUJ
          hLU hbounds w z hw hz hcommon hregular hupdate
      · filter_upwards [] with x heq hxJ
        have hrate : rate (lam iL) (lam iU) = rate a b :=
          Real.log_injOn_pos (mem_Ioi.mpr (rate_pos (hpositive iL) hLU))
            (mem_Ioi.mpr (rate_pos ha hab)) heq
        obtain ⟨hiLa, hiUb⟩ :=
          (rate_eq_of_nested_iff ha (hlam iL).1 hLU (hlam iU).2).mp hrate
        have hiLlo : iL = lo := hinj (hiLa.trans hlo.symm)
        have hiUhi : iU = hi := hinj (hiUb.trans hhi.symm)
        have hloJ : lo ∈ J := by simpa only [hiLlo] using hiLJ
        have hhiJ : hi ∈ J := by simpa only [hiUhi] using hiUJ
        exact ⟨lt_of_le_of_ne ((hw x).1 lo) (Ne.symm ((hxJ lo).mpr hloJ)),
          lt_of_le_of_ne ((hw x).1 hi) (Ne.symm ((hxJ hi).mpr hhiJ))⟩
    · refine ⟨Real.log (rate a b), fun _ => 0, measurable_const,
        fun _ => le_rfl, le_rfl, ?_, ?_⟩
      · filter_upwards [hcommon, hregular] with x hxcommon hxregular
        intro hxJ
        exact (hrealized ⟨x, hxJ, hxcommon, hxregular⟩).elim
      · filter_upwards [hcommon, hregular] with x hxcommon hxregular
        intro _ hxJ
        exact (hrealized ⟨x, hxJ, hxcommon, hxregular⟩).elim
  choose βJ H hH hHnonneg hβJ hbound hendpoint using hcertificates
  have hrates := finite_partition_rates_of_maximal_integral μ T hT (supportClass w)
    (supportClass_measurable w hwmeas) (supportClass_disjoint w) (supportClass_cover w)
    (supportClass_invariant_ae μ T hT lam w z hwmeas hupdate)
    _ hf (Real.log (rate a b)) βJ hβJ H hH hHnonneg hbound hmaximal
  have hendpointAll := ae_all_iff.mpr hendpoint
  filter_upwards [hrates, hendpointAll, hcommon] with x hxrates hxendpoint hxcommon
  obtain ⟨J, hxJ⟩ := supportClass_cover w x
  obtain ⟨hwlo, hwhi⟩ := hxendpoint J (hxrates J hxJ) hxJ
  have hzlo : z x lo ≠ 0 := (not_congr (hxcommon lo)).mp (ne_of_gt hwlo)
  have hzhi : z x hi ≠ 0 := (not_congr (hxcommon hi)).mp (ne_of_gt hwhi)
  exact ⟨hwlo, hwhi, lt_of_le_of_ne ((hz x).1 lo) (Ne.symm hzlo),
    lt_of_le_of_ne ((hz x).1 hi) (Ne.symm hzhi)⟩

/-- Full finite-support classification of maximal invariant BB state
observables: both consecutive normalized spectral measures are the balanced
two-endpoint distribution almost everywhere. -/
theorem finite_spectral_maximal_state
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (hinj : Function.Injective lam) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hregular : ∀ᵐ x ∂μ, 0 < growthSq lam (w x) (z x))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x)
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ)
    (hmaximal : (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) =
      Real.log (rate a b)) :
    ∀ᵐ x ∂μ, (w x lo = 1 / 2 ∧ w x hi = 1 / 2) ∧
      (z x lo = 1 / 2 ∧ z x hi = 1 / 2) ∧
      (∀ i, i ≠ lo → i ≠ hi → w x i = 0 ∧ z x i = 0) := by
  have hpositive := finite_spectral_endpoint_mass_of_maximal_integral μ T hT lam hinj
    lo hi a b ha hab hlo hhi hlam w z hw hz hwmeas hzmeas hregular hupdate hshift hf hmaximal
  exact fixed_face_maximal_state μ T hT lam hinj lo hi a b ha hab hlo hhi hlam
    w z hw hz hwmeas hzmeas hpositive hupdate hshift hf hmaximal

/-- The normalized two-endpoint vector, used for the actual Dirac-law
formulation of maximality. -/
def balancedEndpointWeights (lo hi : ι) : ι → ℝ := by
  classical
  exact fun i => if i = lo ∨ i = hi then 1 / 2 else 0

theorem eq_balancedEndpointWeights {w : ι → ℝ} {lo hi : ι}
    (hlo : w lo = 1 / 2) (hhi : w hi = 1 / 2)
    (hzero : ∀ i, i ≠ lo → i ≠ hi → w i = 0) :
    w = balancedEndpointWeights lo hi := by
  classical
  funext i
  by_cases hilo : i = lo
  · subst i
    simpa only [balancedEndpointWeights, true_or, if_true] using hlo
  · by_cases hihi : i = hi
    · subst i
      simpa only [balancedEndpointWeights, or_true, if_true] using hhi
    · simpa only [balancedEndpointWeights, hilo, hihi, or_self, if_false] using hzero i hilo hihi

/-- Almost-sure equality of the observable pair implies that its probability
law is exactly the Dirac measure at the balanced endpoint pair. -/
theorem map_pair_dirac_of_balanced_ae
    (μ : Measure X) [IsProbabilityMeasure μ] (w z : X → ι → ℝ) (lo hi : ι)
    (hstate : ∀ᵐ x ∂μ, (w x lo = 1 / 2 ∧ w x hi = 1 / 2) ∧
      (z x lo = 1 / 2 ∧ z x hi = 1 / 2) ∧
      (∀ i, i ≠ lo → i ≠ hi → w x i = 0 ∧ z x i = 0)) :
    μ.map (fun x => (w x, z x)) =
      Measure.dirac (balancedEndpointWeights lo hi, balancedEndpointWeights lo hi) := by
  have heq : (fun x => (w x, z x)) =ᵐ[μ]
      (fun _ => (balancedEndpointWeights lo hi, balancedEndpointWeights lo hi)) := by
    filter_upwards [hstate] with x hx
    apply Prod.ext
    · exact eq_balancedEndpointWeights hx.1.1 hx.1.2
        (fun i hnlo hnhi => (hx.2.2 i hnlo hnhi).1)
    · exact eq_balancedEndpointWeights hx.2.1.1 hx.2.1.2
        (fun i hnlo hnhi => (hx.2.2 i hnlo hnhi).2)
  rw [Measure.map_congr heq, Measure.map_const, measure_univ, one_smul]

/-- The full arbitrary-support maximal invariant state law is the balanced
endpoint Dirac measure. For a state space consisting exactly of the two
simplex coordinates, this is the paper's uniqueness statement. -/
theorem finite_spectral_maximal_measure
    (μ : Measure X) [IsProbabilityMeasure μ] (T : X → X)
    (hT : MeasurePreserving T μ μ)
    (lam : ι → ℝ) (hinj : Function.Injective lam) (lo hi : ι) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : X → ι → ℝ)
    (hw : ∀ x, IsSimplex (w x)) (hz : ∀ x, IsSimplex (z x))
    (hwmeas : ∀ i, Measurable (fun x => w x i))
    (hzmeas : ∀ i, Measurable (fun x => z x i))
    (hregular : ∀ᵐ x ∂μ, 0 < growthSq lam (w x) (z x))
    (hupdate : ∀ᵐ x ∂μ, w (T x) = weightUpdate lam (w x) (z x))
    (hshift : ∀ᵐ x ∂μ, z (T x) = w x)
    (hf : Integrable (fun x => Real.log (Real.sqrt (growthSq lam (w x) (z x)))) μ)
    (hmaximal : (∫ x, Real.log (Real.sqrt (growthSq lam (w x) (z x))) ∂μ) =
      Real.log (rate a b)) :
    μ.map (fun x => (w x, z x)) =
      Measure.dirac (balancedEndpointWeights lo hi, balancedEndpointWeights lo hi) := by
  apply map_pair_dirac_of_balanced_ae
  exact finite_spectral_maximal_state μ T hT lam hinj lo hi a b ha hab hlo hhi hlam
    w z hw hz hwmeas hzmeas hregular hupdate hshift hf hmaximal

end BB
