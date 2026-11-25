import BB.PeriodicFull
import BB.WeakLimitTools

/-!
# Genuine empirical probability measures

The weak-limit invariance theorem uses the endpoint telescoping identity and
the mapping theorem for a null discontinuity set. Invariance of a candidate
limit is proved, not postulated.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set BoundedContinuousFunction
open scoped ENNReal Topology BigOperators BoundedContinuousFunction

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

def empiricalProbability (T : X → X) (x : X) (n : ℕ) (hn : 0 < n) : ProbabilityMeasure X :=
  ⟨finiteOrbitMeasure T x n, finite_orbit_probability T x n hn⟩

@[simp] theorem empirical_probability_measure (T : X → X) (x : X) (n : ℕ) (hn : 0 < n) :
    (empiricalProbability T x n hn : Measure X) = finiteOrbitMeasure T x n := rfl

theorem empirical_lintegral (T : X → X) (x : X) (n : ℕ) (hn : 0 < n)
    (q : X → ℝ≥0∞) :
    (∫⁻ y, q y ∂(empiricalProbability T x n hn : Measure X)) =
      (n : ℝ≥0∞)⁻¹ * ∑ k in Finset.range n, q (T^[k] x) := by
  simp only [empirical_probability_measure, finiteOrbitMeasure, lintegral_smul_measure,
    lintegral_finset_sum_measure, lintegral_dirac]

theorem empirical_integral_difference (T : X → X) (x : X) (n : ℕ) (hn : 0 < n)
    (f : X → ℝ) :
    (∫ y, f (T y) ∂(empiricalProbability T x n hn : Measure X)) -
      (∫ y, f y ∂(empiricalProbability T x n hn : Measure X)) =
        (f (T^[n] x) - f x) / (n : ℝ) := by
  rw [empirical_probability_measure, finite_orbit_integral, finite_orbit_integral,
    ← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  simpa only [Function.iterate_succ_apply', Function.iterate_zero_apply] using
    Finset.sum_range_sub (fun k => f (T^[k] x)) n

variable [TopologicalSpace X] [OpensMeasurableSpace X]

theorem empirical_map_integral_difference_le (T : X → X) (hT : Measurable T)
    (x : X) (n : ℕ) (hn : 0 < n) (f : X →ᵇ ℝ) :
    |(∫ y, f y ∂((empiricalProbability T x n hn).map hT.aemeasurable : Measure X)) -
      (∫ y, f y ∂(empiricalProbability T x n hn : Measure X))| ≤
        2 * ‖f‖ / (n : ℝ) := by
  rw [ProbabilityMeasure.toMeasure_map, integral_map hT.aemeasurable f.continuous.measurable.aestronglyMeasurable,
    empirical_integral_difference]
  rw [abs_div, abs_of_pos (show (0 : ℝ) < n by exact_mod_cast hn)]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  calc
    |f (T^[n] x) - f x| ≤ |f (T^[n] x)| + |f x| := abs_sub _ _
    _ ≤ ‖f‖ + ‖f‖ := add_le_add (f.norm_coe_le_norm _) (f.norm_coe_le_norm _)
    _ = 2 * ‖f‖ := by ring

theorem empirical_maps_have_same_limit (T : X → X) (hT : Measurable T)
    (xs : ℕ → X) (ns : ℕ → ℕ) (hn : ∀ j, 0 < ns j)
    (hns : Tendsto ns atTop atTop) (μ : ProbabilityMeasure X)
    (hlim : Tendsto (fun j => empiricalProbability T (xs j) (ns j) (hn j)) atTop (𝓝 μ)) :
    Tendsto (fun j => (empiricalProbability T (xs j) (ns j) (hn j)).map hT.aemeasurable)
      atTop (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hμ := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim f
  have hdiff : Tendsto (fun j =>
      (∫ y, f y ∂((empiricalProbability T (xs j) (ns j) (hn j)).map hT.aemeasurable : Measure X)) -
      (∫ y, f y ∂(empiricalProbability T (xs j) (ns j) (hn j) : Measure X))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun j => ?_)
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => 2 * ‖f‖) atTop (𝓝 (2 * ‖f‖))).div_atTop
        (tendsto_natCast_atTop_atTop.comp hns))
    exact empirical_map_integral_difference_le T hT (xs j) (ns j) (hn j) f
  have h := hdiff.add hμ
  simpa only [sub_add_cancel, zero_add] using h

theorem empirical_limit_invariant [BorelSpace X] [HasOuterApproxClosed X]
    (T : X → X) (hT : Measurable T) (xs : ℕ → X) (ns : ℕ → ℕ)
    (hn : ∀ j, 0 < ns j) (hns : Tendsto ns atTop atTop) (μ : ProbabilityMeasure X)
    (hlim : Tendsto (fun j => empiricalProbability T (xs j) (ns j) (hn j)) atTop (𝓝 μ))
    (D : Set X) (hD : (μ : Measure X) D = 0) (hc : ∀ x ∉ D, ContinuousAt T x) :
    MeasurePreserving T (μ : Measure X) (μ : Measure X) := by
  have hsame := empirical_maps_have_same_limit T hT xs ns hn hns μ hlim
  have hmap := probability_map_tendsto_of_null_discontinuities hlim T hT D hD hc
  have he : μ.map hT.aemeasurable = μ := tendsto_nhds_unique hmap hsame
  exact ⟨hT, congrArg (fun ν : ProbabilityMeasure X => (ν : Measure X)) he⟩

end BB
