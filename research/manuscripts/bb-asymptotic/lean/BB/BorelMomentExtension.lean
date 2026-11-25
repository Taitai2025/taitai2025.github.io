import BB.OperatorMoments
import BB.RieszRepresentation

/-!
# Extending moment identities to bounded Borel tests

Finite scalar measures on a compact real interval are determined by their
polynomial moments. Consequently every finite real linear relation between
those moments holds for all bounded Borel tests. This supplies the genuine
measure-theoretic passage used to construct weighted operator quadratic forms.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal ENNReal BigOperators Polynomial

section FiniteIntegral
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [OpensMeasurableSpace K]

lemma continuous_integrable_finite (μ : FiniteMeasure K) (f : C(K, ℝ)) :
    Integrable f (μ : Measure K) := (mkOfCompact f).integrable (μ : Measure K)

def finiteIntegralLinear (μ : FiniteMeasure K) : C(K, ℝ) →ₗ[ℝ] ℝ where
  toFun f := ∫ x, f x ∂(μ : Measure K)
  map_add' f g := integral_add (continuous_integrable_finite μ f) (continuous_integrable_finite μ g)
  map_smul' c f := integral_smul c f

def finiteIntegralDual (μ : FiniteMeasure K) : NormedSpace.Dual ℝ C(K, ℝ) :=
  (finiteIntegralLinear μ).mkContinuous ((μ : Measure K) univ).toReal (by
    intro f
    have h := norm_integral_le_of_norm_le_const (μ := (μ : Measure K))
      (Filter.eventually_of_forall (fun x => f.norm_coe_le_norm x))
    simpa only [finiteIntegralLinear, LinearMap.coe_mk, AddHom.coe_mk, mul_comm] using h)

@[simp] lemma finiteIntegralDual_apply (μ : FiniteMeasure K) (f : C(K, ℝ)) :
    finiteIntegralDual μ f = ∫ x, f x ∂(μ : Measure K) := rfl

lemma finite_measure_eq_of_continuous_integrals [HasOuterApproxClosed K] [BorelSpace K]
    (μ ν : FiniteMeasure K)
    (h : ∀ f : C(K, ℝ), (∫ x, f x ∂(μ : Measure K)) = ∫ x, f x ∂(ν : Measure K)) : μ = ν := by
  have ht : Tendsto (fun _ : ℕ => μ) atTop (𝓝 ν) := by
    apply FiniteMeasure.tendsto_iff_forall_integral_tendsto.mpr
    intro f
    have heq := h f.toContinuousMap
    change (∫ x, f x ∂(μ : Measure K)) = ∫ x, f x ∂(ν : Measure K) at heq
    change Tendsto (fun _ : ℕ => ∫ x, f x ∂(μ : Measure K)) atTop (𝓝 (∫ x, f x ∂(ν : Measure K)))
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique tendsto_const_nhds ht

lemma bounded_measurable_integrable_finite (μ : FiniteMeasure K) (f : K → ℝ)
    (hf : Measurable f) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C) : Integrable f (μ : Measure K) :=
  (integrable_const C).mono' hf.aestronglyMeasurable (Filter.eventually_of_forall hC)

end FiniteIntegral

/-- Polynomial density determines any continuous linear functional, without
positivity or normalization restrictions. -/
theorem interval_dual_eq_of_moments (a b : ℝ)
    (L M : NormedSpace.Dual ℝ C(Icc a b, ℝ))
    (h : ∀ k : ℕ, L ((intervalCoordinate a b)^k) = M ((intervalCoordinate a b)^k)) : L = M := by
  have hpoly : ∀ p : ℝ[X], L (p.toContinuousMapOn (Icc a b)) = M (p.toContinuousMapOn (Icc a b)) := by
    intro p
    induction p using Polynomial.induction_on' with
    | h_add p q hp hq =>
      have he : (p + q).toContinuousMapOn (Icc a b) =
          p.toContinuousMapOn (Icc a b) + q.toContinuousMapOn (Icc a b) := by
        ext t
        simp
      rw [he, map_add, map_add, hp, hq]
    | h_monomial k c =>
      rw [continuous_polynomial_monomial, _root_.map_smul, _root_.map_smul, h k]
  have hd : Dense (polynomialFunctions (Icc a b) : Set C(Icc a b, ℝ)) := by
    rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, polynomialFunctions_closure_eq_top]
    rfl
  have hsub : (polynomialFunctions (Icc a b) : Set C(Icc a b, ℝ)) ⊆ {f | L f = M f} := by
    intro f hf
    rw [polynomialFunctions_coe] at hf
    obtain ⟨p, rfl⟩ := hf
    exact hpoly p
  have hcl := closure_minimal hsub (isClosed_eq L.continuous M.continuous)
  exact DFunLike.ext _ _ (fun f => hcl (hd f))

/-- Finite Borel measures on a compact interval are determined by all their moments. -/
theorem finite_measure_eq_of_moments (a b : ℝ) (μ ν : FiniteMeasure (Icc a b))
    (h : ∀ k : ℕ, (∫ t, (t : ℝ)^k ∂(μ : Measure (Icc a b))) =
      ∫ t, (t : ℝ)^k ∂(ν : Measure (Icc a b))) : μ = ν := by
  have hdual : finiteIntegralDual μ = finiteIntegralDual ν := by
    apply interval_dual_eq_of_moments a b
    intro k
    simpa only [finiteIntegralDual_apply, ContinuousMap.pow_apply, intervalCoordinate] using h k
  apply finite_measure_eq_of_continuous_integrals
  intro f
  exact congrArg (fun L : NormedSpace.Dual ℝ C(Icc a b, ℝ) => L f) hdual

section LinearCombination
variable {K : Type*} [MeasurableSpace K]
variable {ι : Type*} [Fintype ι]

/-- Positive part of a finite real linear combination of positive finite measures. -/
def positiveMeasureCombination (μ : ι → FiniteMeasure K) (c : ι → ℝ) : FiniteMeasure K :=
  ∑ i, (c i).toNNReal • μ i

lemma finiteMeasure_coe_sum (μ : ι → FiniteMeasure K) :
    ((∑ i, μ i : FiniteMeasure K) : Measure K) = ∑ i, (μ i : Measure K) := by
  exact map_sum FiniteMeasure.toMeasureAddMonoidHom μ Finset.univ

lemma integral_positiveMeasureCombination (μ : ι → FiniteMeasure K) (c : ι → ℝ)
    (f : K → ℝ) (hf : ∀ i, Integrable f (μ i : Measure K)) :
    (∫ x, f x ∂(positiveMeasureCombination μ c : Measure K)) =
      ∑ i, ((c i).toNNReal : ℝ) * ∫ x, f x ∂(μ i : Measure K) := by
  rw [positiveMeasureCombination, finiteMeasure_coe_sum]
  simp only [FiniteMeasure.toMeasure_smul]
  rw [integral_finset_sum_measure (fun i _ => (hf i).smul_measure_nnreal)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]

lemma positive_negative_split (c v : ι → ℝ) :
    (∑ i, ((c i).toNNReal : ℝ) * v i) - (∑ i, ((-c i).toNNReal : ℝ) * v i) = ∑ i, c i * v i := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← sub_mul, Real.coe_toNNReal', Real.coe_toNNReal']
  by_cases h : 0 ≤ c i
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · have hneg : 0 ≤ -c i := neg_nonneg.mpr (le_of_not_ge h)
    rw [max_eq_right (le_of_not_ge h), max_eq_left hneg]
    ring

end LinearCombination

/-- Every finite real linear relation between scalar moments extends to every
test integrable against the individual measures, in particular bounded Borel tests. -/
theorem integral_relation_of_moments (a b : ℝ) {ι : Type*} [Fintype ι]
    (μ : ι → FiniteMeasure (Icc a b)) (c : ι → ℝ)
    (h : ∀ k : ℕ, (∑ i, c i * ∫ t, (t : ℝ)^k ∂(μ i : Measure (Icc a b))) = 0)
    (f : Icc a b → ℝ) (hf : ∀ i, Integrable f (μ i : Measure (Icc a b))) :
    (∑ i, c i * ∫ t, f t ∂(μ i : Measure (Icc a b))) = 0 := by
  have heq : positiveMeasureCombination μ c = positiveMeasureCombination μ (fun i => -c i) := by
    apply finite_measure_eq_of_moments a b
    intro k
    have hk : ∀ i, Integrable (fun t : Icc a b => (t : ℝ)^k) (μ i : Measure (Icc a b)) := by
      intro i
      exact continuous_integrable_finite (μ i) ((intervalCoordinate a b)^k)
    rw [integral_positiveMeasureCombination μ c _ hk,
      integral_positiveMeasureCombination μ (fun i => -c i) _ hk]
    have hs := positive_negative_split c (fun i => ∫ t, (t : ℝ)^k ∂(μ i : Measure (Icc a b)))
    rw [h k] at hs
    exact sub_eq_zero.mp hs
  have htest := congrArg (fun ν : FiniteMeasure (Icc a b) => ∫ t, f t ∂(ν : Measure (Icc a b))) heq
  dsimp only at htest
  rw [integral_positiveMeasureCombination μ c f hf,
    integral_positiveMeasureCombination μ (fun i => -c i) f hf] at htest
  have hs := positive_negative_split c (fun i => ∫ t, f t ∂(μ i : Measure (Icc a b)))
  rw [htest, sub_self] at hs
  exact hs.symm

end BB
