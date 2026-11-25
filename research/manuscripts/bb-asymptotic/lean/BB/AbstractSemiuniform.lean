import BB.LowerSemicontinuousLoss
import BB.UpperSemicontinuousIntegral
import Mathlib.Algebra.BigOperators.WithTop

/-!
# General semiuniform ergodic bound with singularities

This is the manuscript's abstract proposition on a compact metric space,
with the actual extended integral and no added continuity or integrability
assumption. The bound holds for all segments: if one term is minus infinity,
the finite sum is minus infinity and the inequality follows automatically.
-/

noncomputable section
namespace BB
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators

theorem ereal_coe_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i in s, f i : ℝ) : EReal) = ∑ i in s, (f i : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, EReal.coe_add, ih]

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]

theorem empirical_upper_defect_formula (T : X → X) (x : X) (n : ℕ) (hn : 0 < n)
    (C : ℝ) (f : X → EReal) (hC : ∀ y, f y ≤ (C : EReal))
    (hfinite : ∀ k < n, f (T^[k] x) ≠ ⊥) :
    (∫⁻ y, upperDefect C f y ∂(empiricalProbability T x n hn : Measure X)) =
      ENNReal.ofReal (C - (∑ k in Finset.range n, (f (T^[k] x)).toReal) / (n : ℝ)) := by
  have hr (k : ℕ) (hk : k < n) : (f (T^[k] x)).toReal ≤ C := by
    have ht : f (T^[k] x) ≠ ⊤ := ne_of_lt ((hC _).trans_lt (EReal.coe_lt_top C))
    exact EReal.coe_le_coe_iff.mp ((EReal.coe_toReal ht (hfinite k hk)) ▸ hC _)
  rw [empirical_lintegral]
  have he : (∑ k in Finset.range n, upperDefect C f (T^[k] x)) =
      ENNReal.ofReal (∑ k in Finset.range n, (C - (f (T^[k] x)).toReal)) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun k hk => sub_nonneg.mpr (hr k (Finset.mem_range.mp hk)))]
    apply Finset.sum_congr rfl
    intro k hk
    exact if_neg (hfinite k (Finset.mem_range.mp hk))
  rw [he]
  have hnp : (0 : ℝ) < n := by exact_mod_cast hn
  calc
    _ = ENNReal.ofReal ((∑ k in Finset.range n, (C - (f (T^[k] x)).toReal)) / (n : ℝ)) := by
      rw [ENNReal.ofReal_div_of_pos hnp, ENNReal.ofReal_natCast, div_eq_mul_inv, mul_comm]
    _ = _ := by
      congr 1
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      ring

variable [MetricSpace X] [CompactSpace X] [BorelSpace X]

/-- The abstract semiuniform principle in the source. Its invariant-measure
hypothesis is required only for finite extended averages. A finite additive
constant is obtained uniformly in the initial state and segment length. -/
theorem abstract_semiuniform (T : X → X) (hT : Measurable T) (D : Set X)
    (hc : ∀ x ∉ D, ContinuousAt T x) (f : X → EReal)
    (hf : UpperSemicontinuous f) (C : ℝ) (hC : ∀ x, f x ≤ (C : EReal))
    (hD : ∀ x ∈ D, f x = ⊥) (β : ℝ)
    (hinv : ∀ μ : ProbabilityMeasure X,
      MeasurePreserving T (μ : Measure X) (μ : Measure X) →
      ⊥ < boundedAboveIntegral C f (μ : Measure X) →
      boundedAboveIntegral C f (μ : Measure X) ≤ (β : EReal))
    (η : ℝ) (hη : 0 < η) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (n : ℕ) (x : X),
      (∑ k in Finset.range n, f (T^[k] x)) ≤ (((n : ℝ) * (β + η) + B : ℝ) : EReal) := by
  have hq : LowerSemicontinuous (upperDefect C f) :=
    upper_defect_lowerSemicontinuous C f hC hf
  have hqD : ∀ x ∈ D, upperDefect C f x = ⊤ :=
    fun x hx => (upper_defect_top_iff C f x).mpr (hD x hx)
  have hqi : ∀ μ : ProbabilityMeasure X,
      MeasurePreserving T (μ : Measure X) (μ : Measure X) →
      (∫⁻ x, upperDefect C f x ∂(μ : Measure X)) ≠ ⊤ →
      ENNReal.ofReal (C - β) ≤ ∫⁻ x, upperDefect C f x ∂(μ : Measure X) := by
    intro μ hp hfin
    have hbot : boundedAboveIntegral C f (μ : Measure X) ≠ ⊥ :=
      mt (bounded_above_integral_eq_bot_iff C f (μ : Measure X)).mp hfin
    have hi := hinv μ hp (bot_lt_iff_ne_bot.mpr hbot)
    rw [bounded_above_integral_finite_formula C f (μ : Measure X) hfin] at hi
    apply ENNReal.ofReal_le_of_le_toReal
    have hr := EReal.coe_le_coe_iff.mp hi
    linarith
  obtain ⟨N, hN⟩ := semicontinuous_loss_eventual_mean_lower T hT D hc
    (upperDefect C f) hq hqD (C - β) hqi η hη
  let B : ℝ := (N : ℝ) * max (C - (β + η)) 0
  have hB : 0 ≤ B := mul_nonneg (Nat.cast_nonneg N) (le_max_right _ _)
  refine ⟨B, hB, ?_⟩
  intro n x
  by_cases hsmall : n ≤ N
  · have hs : (∑ k in Finset.range n, f (T^[k] x)) ≤ (((n : ℝ) * C : ℝ) : EReal) := by
      calc
        _ ≤ ∑ _k in Finset.range n, (C : EReal) := Finset.sum_le_sum (fun k _ => hC _)
        _ = _ := by rw [← ereal_coe_finset_sum]; simp
    apply hs.trans
    apply EReal.coe_le_coe_iff.mpr
    have h1 := mul_le_mul_of_nonneg_left (le_max_left (C - (β + η)) 0) (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    have h2 := mul_le_mul_of_nonneg_right (show (n : ℝ) ≤ N by exact_mod_cast hsmall)
      (le_max_right (C - (β + η)) 0)
    change (n : ℝ) * C ≤ (n : ℝ) * (β + η) + (N : ℝ) * max (C - (β + η)) 0
    nlinarith
  · by_cases hbot : ∃ k ∈ Finset.range n, f (T^[k] x) = ⊥
    · have hs : (∑ k in Finset.range n, f (T^[k] x)) = ⊥ := WithBot.sum_eq_bot_iff.mpr hbot
      rw [hs]
      exact bot_le
    · have hfinite : ∀ k < n, f (T^[k] x) ≠ ⊥ := by
        intro k hk hb
        exact hbot ⟨k, Finset.mem_range.mpr hk, hb⟩
      have hn : 0 < n := by omega
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have hm : N ≤ m := by omega
      have hg := hN m hm x
      rw [empirical_upper_defect_formula T x (m + 1) (Nat.succ_pos m) C f hC hfinite] at hg
      have hr (k : ℕ) (hk : k < m + 1) : (f (T^[k] x)).toReal ≤ C := by
        have ht : f (T^[k] x) ≠ ⊤ := ne_of_lt ((hC _).trans_lt (EReal.coe_lt_top C))
        exact EReal.coe_le_coe_iff.mp ((EReal.coe_toReal ht (hfinite k hk)) ▸ hC _)
      have hs : (∑ k in Finset.range (m + 1), (f (T^[k] x)).toReal) ≤ ((m + 1 : ℕ) : ℝ) * C := by
        calc
          _ ≤ ∑ _k in Finset.range (m + 1), C :=
            Finset.sum_le_sum (fun k hk => hr k (Finset.mem_range.mp hk))
          _ = _ := by simp
      have hmp : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have havg : (∑ k in Finset.range (m + 1), (f (T^[k] x)).toReal) /
          ((m + 1 : ℕ) : ℝ) ≤ C := (div_le_iff hmp).mpr (by nlinarith)
      have hg' := (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr havg)).mp hg
      have hmean : (∑ k in Finset.range (m + 1), (f (T^[k] x)).toReal) /
          ((m + 1 : ℕ) : ℝ) ≤ β + η := by linarith
      have htotal := (div_le_iff hmp).mp hmean
      have he : (∑ k in Finset.range (m + 1), f (T^[k] x)) =
          ((∑ k in Finset.range (m + 1), (f (T^[k] x)).toReal : ℝ) : EReal) := by
        rw [ereal_coe_finset_sum]
        apply Finset.sum_congr rfl
        intro k hk
        have ht : f (T^[k] x) ≠ ⊤ := ne_of_lt ((hC _).trans_lt (EReal.coe_lt_top C))
        exact (EReal.coe_toReal ht (hfinite k (Finset.mem_range.mp hk))).symm
      rw [he]
      apply EReal.coe_le_coe_iff.mpr
      nlinarith

end BB
