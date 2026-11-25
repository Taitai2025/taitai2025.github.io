import Mathlib

set_option autoImplicit false

open Set Filter Function
open scoped Topology

namespace Research.CompactCone

/-- Pointwise decay of continuous orbit radii on a compact set gives a bounded
time to reach a radius strictly below one half. -/
theorem boundedEntry {X : Type*} [TopologicalSpace X]
    (T : X → X) (r : X → ℝ) (S : Set X)
    (compact : IsCompact S) (continuousT : Continuous T) (continuousR : Continuous r)
    (pointwise : ∀ x ∈ S, Tendsto (fun n : ℕ => r ((T^[n]) x)) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ S, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ r ((T^[j]) x) ≤ 1 / 2 := by
  let U (i : ℕ) := {x : X | r ((T^[i+1]) x) < 1 / 2}
  have openU (i : ℕ) : IsOpen (U i) :=
    isOpen_lt (continuousR.comp (continuousT.iterate (i + 1))) continuous_const
  have covered : S ⊆ ⋃ i, U i := by
    intro x hx
    have eventuallySmall := (tendsto_order.1 (pointwise x hx)).2 (1 / 2) (by norm_num)
    obtain ⟨n, hn⟩ := eventually_atTop.1 eventuallySmall
    exact mem_iUnion.2 ⟨n, hn (n + 1) (by omega)⟩
  obtain ⟨indices, finiteCover⟩ := compact.elim_finite_subcover U openU covered
  refine ⟨indices.sup id + 1, by omega, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.1 (finiteCover hx)
  obtain ⟨hin, small⟩ := mem_iUnion.1 hi
  have bound : i ≤ indices.sup id := Finset.le_sup (f := id) hin
  exact ⟨i + 1, by omega, Nat.succ_le_succ bound, le_of_lt small⟩

/-- Radius growth accumulated over a specified number of iterations. -/
theorem orbitGrowth {X : Type*} (T : X → X) (r : X → ℝ) (B : ℝ)
    (nonnegB : 0 ≤ B) (step : ∀ x, r (T x) ≤ B * r x) (k : ℕ) (x : X) :
    r ((T^[k]) x) ≤ B ^ k * r x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    calc
      r (T ((T^[k]) x)) ≤ B * r ((T^[k]) x) := step _
      _ ≤ B * (B ^ k * r x) := mul_le_mul_of_nonneg_left ih nonnegB
      _ = B ^ (k + 1) * r x := by rw [pow_succ]; ring

private theorem powerFromLe {D : ℝ} (hD : 1 ≤ D) {n m : ℕ} (h : n ≤ m) :
    D ^ n ≤ D ^ m := by
  have nonneg : 0 ≤ D := by linarith
  have extra : 1 ≤ D ^ (m - n) := by
    induction (m - n) with
    | zero => simp
    | succ j ih =>
      rw [pow_succ]
      calc
        1 ≤ D * 1 := by simpa using hD
        _ ≤ D * D ^ j := mul_le_mul_of_nonneg_left ih nonneg
        _ = D ^ j * D := mul_comm _ _
  calc
    D ^ n = D ^ n * 1 := by rw [mul_one]
    _ ≤ D ^ n * D ^ (m - n) := mul_le_mul_of_nonneg_left extra (pow_nonneg nonneg _)
    _ = D ^ m := by rw [← pow_add, Nat.add_sub_of_le h]

/-- Uniform exponential rate from bounded entry and bounded one-step growth.
The input rho is any positive factor whose N-th power is at least one half. -/
theorem rateFromEntry {X : Type*} (T : X → X) (r : X → ℝ) (B ρ : ℝ) (N : ℕ)
    (nonneg : ∀ x, 0 ≤ r x) (hB : 1 ≤ B) (pos : 0 < ρ) (subunit : ρ ≤ 1)
    (threshold : 1 / 2 ≤ ρ ^ N)
    (step : ∀ x, r (T x) ≤ B * r x)
    (entry : ∀ x, ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ r ((T^[j]) x) ≤ (1 / 2) * r x) :
    ∀ k x, r ((T^[k]) x) ≤ (B / ρ) ^ N * ρ ^ k * r x := by
  have nonnegB : 0 ≤ B := by linarith
  have hD : 1 ≤ B / ρ := (le_div_iff pos).2 (by simpa using subunit.trans hB)
  have hC : 1 ≤ (B / ρ) ^ N := by simpa using powerFromLe hD (Nat.zero_le N)
  have nonnegC : 0 ≤ (B / ρ) ^ N := by linarith
  intro k
  induction k using Nat.strong_induction_on with
  | h k smaller =>
    intro x
    obtain ⟨j, posJ, boundJ, contracts⟩ := entry x
    by_cases jLe : j ≤ k
    · have hj : k - j < k := by omega
      have split : k - j + j = k := Nat.sub_add_cancel jLe
      have hjpow : (1 / 2 : ℝ) ≤ ρ ^ j := by
        refine threshold.trans ?_
        have rest : ρ ^ (N - j) ≤ 1 := by
          induction (N - j) with
          | zero => simp
          | succ v ih =>
            rw [pow_succ]
            calc
              ρ ^ v * ρ ≤ 1 * ρ := mul_le_mul_of_nonneg_right ih pos.le
              _ ≤ 1 := by simpa using subunit
        calc
          ρ ^ N = ρ ^ j * ρ ^ (N - j) := by rw [← pow_add, Nat.add_sub_of_le boundJ]
          _ ≤ ρ ^ j := by simpa using mul_le_mul_of_nonneg_left rest (pow_nonneg pos.le j)
      have small := contracts.trans (mul_le_mul_of_nonneg_right hjpow (nonneg x))
      calc
        r ((T^[k]) x) = r ((T^[k - j]) ((T^[j]) x)) := by
          rw [← Function.iterate_add_apply, split]
        _ ≤ (B / ρ) ^ N * ρ ^ (k - j) * r ((T^[j]) x) :=
          smaller (k - j) hj _
        _ ≤ (B / ρ) ^ N * ρ ^ (k - j) * (ρ ^ j * r x) :=
          mul_le_mul_of_nonneg_left small (mul_nonneg nonnegC (pow_nonneg pos.le _))
        _ = (B / ρ) ^ N * (ρ ^ (k - j) * ρ ^ j) * r x := by ring
        _ = (B / ρ) ^ N * ρ ^ k * r x := by rw [← pow_add, split]
    · have hkN : k ≤ N := by omega
      have multiplyBound := mul_le_mul_of_nonneg_right (powerFromLe hD hkN)
        (mul_nonneg (pow_nonneg pos.le k) (nonneg x))
      calc
        r ((T^[k]) x) ≤ B ^ k * r x := orbitGrowth T r B nonnegB step k x
        _ = (B / ρ) ^ k * (ρ ^ k * r x) := by
          rw [div_pow]
          field_simp [ne_of_gt pos] <;> ring
        _ ≤ (B / ρ) ^ N * (ρ ^ k * r x) := multiplyBound
        _ = (B / ρ) ^ N * ρ ^ k * r x := by ring

/-- A contractive factor exists for each finite entry horizon. -/
theorem existsRate (N : ℕ) : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ 1 / 2 ≤ ρ ^ N := by
  let δ : ℝ := 1 / (2 * ((N : ℝ) + 1))
  let ρ := 1 - δ
  have denpos : 0 < 2 * ((N : ℝ) + 1) := by positivity
  have δpos : 0 < δ := div_pos one_pos denpos
  have δsmall : δ ≤ 1 / 2 := (div_le_iff denpos).2 (by linarith)
  have ρpos : 0 < ρ := by dsimp [ρ]; linarith
  have below (n : ℕ) : 1 - (n : ℝ) * δ ≤ ρ ^ n := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        1 - ((n + 1 : ℕ) : ℝ) * δ ≤ (1 - (n : ℝ) * δ) * ρ := by
          rw [Nat.cast_add, Nat.cast_one]
          dsimp [ρ]
          nlinarith [mul_nonneg (Nat.cast_nonneg n : 0 ≤ (n : ℝ)) (sq_nonneg δ)]
        _ ≤ ρ ^ n * ρ := mul_le_mul_of_nonneg_right ih ρpos.le
        _ = ρ ^ (n + 1) := (pow_succ _ _).symm
  have last : (N : ℝ) * δ ≤ 1 / 2 := by
    dsimp [δ]
    rw [mul_one_div]
    exact (div_le_iff denpos).2 (by linarith)
  exact ⟨ρ, ρpos, by dsimp [ρ]; linarith, (by linarith : 1 / 2 ≤ 1 - (N : ℝ) * δ).trans (below N)⟩

/-- Compact normalize-and-rescale criterion. The normalization identity is
required for the whole forward orbit; a one-step scalar equality is insufficient. -/
theorem uniformRate {X : Type*} [TopologicalSpace X]
    (T : X → X) (r : X → ℝ) (S : Set X)
    (compact : IsCompact S) (continuousT : Continuous T) (continuousR : Continuous r)
    (nonneg : ∀ x, 0 ≤ r x) (zeroPreserved : ∀ x, r x = 0 → r (T x) = 0)
    (represent : ∀ x, 0 < r x →
      ∃ y ∈ S, ∀ k : ℕ, r ((T^[k]) x) = r x * r ((T^[k]) y))
    (pointwise : ∀ x ∈ S, Tendsto (fun n : ℕ => r ((T^[n]) x)) atTop (𝓝 0)) :
    ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (k : ℕ) x, r ((T^[k]) x) ≤ C * ρ ^ k * r x := by
  obtain ⟨N, hN, stops⟩ := boundedEntry T r S compact continuousT continuousR pointwise
  have bounded : BddAbove ((r ∘ T) '' S) :=
    (compact.image (continuousR.comp continuousT)).bddAbove
  obtain ⟨K, upper⟩ := bounded
  let B := max 1 K
  have hB : 1 ≤ B := le_max_left _ _
  have step (x : X) : r (T x) ≤ B * r x := by
    by_cases hx : r x = 0
    · simp [zeroPreserved x hx, hx]
    · obtain ⟨y, hy, equiv⟩ := represent x (lt_of_le_of_ne (nonneg x) (Ne.symm hx))
      have hk : r (T y) ≤ K := upper ⟨y, hy, rfl⟩
      have first : r (T x) = r x * r (T y) := by simpa using equiv 1
      rw [first, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hk.trans (le_max_right _ _)) (nonneg x)
  have entry (x : X) : ∃ j : ℕ, 0 < j ∧ j ≤ N ∧ r ((T^[j]) x) ≤ (1 / 2) * r x := by
    by_cases hx : r x = 0
    · exact ⟨1, by omega, by omega, by simpa [hx] using le_of_eq (zeroPreserved x hx)⟩
    · obtain ⟨y, hy, equiv⟩ := represent x (lt_of_le_of_ne (nonneg x) (Ne.symm hx))
      obtain ⟨j, hj, hjN, small⟩ := stops y hy
      refine ⟨j, hj, hjN, ?_⟩
      rw [equiv j, mul_comm (1 / 2)]
      exact mul_le_mul_of_nonneg_left small (nonneg x)
  obtain ⟨ρ, hρ, hρ1, hρN⟩ := existsRate N
  have hD : 1 ≤ B / ρ := (le_div_iff hρ).2 (by simpa using hρ1.le.trans hB)
  refine ⟨(B / ρ) ^ N, ρ, by simpa using powerFromLe hD (Nat.zero_le N), hρ, hρ1, ?_⟩
  exact rateFromEntry T r B ρ N nonneg hB hρ hρ1.le hρN step entry

#print axioms boundedEntry
#print axioms rateFromEntry
#print axioms existsRate
#print axioms uniformRate

/-- Scaling as a map on a closed cone. The closure under nonnegative scalars is
kept explicit, so the cone need not be convex or span the ambient space. -/
def scaleCone {E : Type*} [SMul ℝ E] {cone : Set E}
    (stable : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ cone, a • x ∈ cone)
    (a : ℝ) (nonneg : 0 ≤ a) (x : cone) : cone :=
  ⟨a • x.val, stable a nonneg x.val x.property⟩

/-- Uniform exponential convergence for a continuous, positively homogeneous
self-map of a finite-dimensional closed cone, including the zero cone. -/
theorem closedConeRate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (cone : Set E) (closed : IsClosed cone)
    (stable : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ cone, a • x ∈ cone)
    (T : cone → cone) (continuousT : Continuous T)
    (homogeneous : ∀ (a : ℝ) (ha : 0 ≤ a) (x : cone),
      (T (scaleCone stable a ha x)).val = a • (T x).val)
    (pointwise : ∀ x : cone, Tendsto (fun k : ℕ => ((T^[k]) x).val) atTop (𝓝 (0 : E))) :
    ∃ C ρ : ℝ, 1 ≤ C ∧ 0 < ρ ∧ ρ < 1 ∧
      ∀ (k : ℕ) (x : cone), ‖((T^[k]) x).val‖ ≤ C * ρ ^ k * ‖x.val‖ := by
  let S : Set cone := Subtype.val ⁻¹' Metric.sphere (0 : E) 1
  let r (x : cone) : ℝ := ‖x.val‖
  have compactS : IsCompact S := closed.closedEmbedding_subtype_val.isCompact_preimage
    (isCompact_sphere (0 : E) 1)
  have zeroPreserved (x : cone) (hx : r x = 0) : r (T x) = 0 := by
    have eqZero : x.val = 0 := norm_eq_zero.mp hx
    have scaleSame : scaleCone stable 0 le_rfl x = x := by
      apply Subtype.ext
      change (0 : ℝ) • x.val = x.val
      rw [zero_smul, eqZero]
    have hm := homogeneous 0 le_rfl x
    rw [scaleSame, zero_smul] at hm
    exact norm_eq_zero.mpr hm
  have mappedScale (a : ℝ) (ha : 0 ≤ a) (x : cone) (k : ℕ) :
      (T^[k]) (scaleCone stable a ha x) = scaleCone stable a ha ((T^[k]) x) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
      exact Subtype.ext (homogeneous a ha _)
  have representatives (x : cone) (hx : 0 < r x) :
      ∃ y ∈ S, ∀ k : ℕ, r ((T^[k]) x) = r x * r ((T^[k]) y) := by
    let y := scaleCone stable (r x)⁻¹ (inv_nonneg.mpr hx.le) x
    have ynorm : ‖y.val‖ = 1 := by
      change ‖(r x)⁻¹ • x.val‖ = 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx)]
      exact inv_mul_cancel (ne_of_gt hx)
    have ys : y ∈ S := by simpa [S, Metric.mem_sphere, dist_zero_right] using ynorm
    have back : scaleCone stable (r x) hx.le y = x := by
      apply Subtype.ext
      change r x • ((r x)⁻¹ • x.val) = x.val
      rw [smul_smul, mul_inv_cancel (ne_of_gt hx), one_smul]
    refine ⟨y, ys, fun k => ?_⟩
    calc
      r ((T^[k]) x) = r ((T^[k]) (scaleCone stable (r x) hx.le y)) := by rw [back]
      _ = r x * r ((T^[k]) y) := by
        rw [mappedScale]
        change ‖r x • ((T^[k]) y).val‖ = r x * ‖((T^[k]) y).val‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hx]
  have radii (x : cone) (_ : x ∈ S) :
      Tendsto (fun k : ℕ => r ((T^[k]) x)) atTop (𝓝 0) := by
    simpa [r, Function.comp_def] using continuous_norm.continuousAt.tendsto.comp (pointwise x)
  exact uniformRate T r S compactS continuousT
    (continuous_norm.comp continuous_subtype_val) (fun _ => norm_nonneg _)
    zeroPreserved representatives radii

#print axioms closedConeRate

end Research.CompactCone
