import Mathlib

/-!
Algebraic interfaces for the rank-boundary proof in arXiv:2609.12114v1,
Section 8.  Finite spectral sets may be supplied as the index type.
The matrix Cauchy--Binet identity and the topology of endpoint maps are NOT
assumed to be proved by this file.  Every hypothesis is explicit.
-/
namespace LMSDRankBoundary

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- Unnormalized subset mass, with `x i` representing a squared block norm. -/
def mass (c : ℝ) (x : ι → ℝ) (s : Finset ι) : ℝ :=
  c * ∏ i in s, x i

/-- The exchange cross-product identity includes zero common factors. -/
theorem product_exchange_identity (K : Finset ι) (h r : ι)
    (hh : h ∉ K) (hr : r ∉ K) (cI cJ : ℝ) (x : ι → ℝ) :
    mass cI x (insert h K) * (cJ * x r) =
      (cI * x h) * mass cJ x (insert r K) := by
  simp only [mass, Finset.prod_insert hh, Finset.prod_insert hr]
  ring

/-- A normalized coefficient is nonnegative. -/
theorem normalized_nonnegative (a D : ℝ) (ha : 0 ≤ a) (hD : 0 < D) :
    0 ≤ a / D := div_nonneg ha (le_of_lt hD)

/-- The sum of all normalized finite masses equals one. -/
theorem normalized_sum_one (s : Finset ι) (b : ι → ℝ)
    (hD : 0 < ∑ i in s, b i) :
    (∑ i in s, b i / (∑ j in s, b j)) = 1 := by
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt hD)

/-- The denominator dominates every nonnegative mass in its defining sum. -/
theorem mass_le_total (s : Finset ι) (b : ι → ℝ)
    (hb : ∀ i ∈ s, 0 ≤ b i) (j : ι) (hj : j ∈ s) :
    b j ≤ ∑ i in s, b i := by
  exact Finset.single_le_sum hb hj

/-- Core exchange estimate.  The cross-product equality is an explicit input;
    `product_exchange_identity` supplies it for product masses. -/
theorem exchange_probability_bound (a b D cI cJ xh xr : ℝ)
    (ha : 0 ≤ a) (hD : 0 < D) (hbD : b ≤ D)
    (hcI : 0 ≤ cI) (hcJ : 0 < cJ) (hxh : 0 ≤ xh) (hxr : 0 < xr)
    (hex : a * (cJ * xr) = (cI * xh) * b) :
    0 ≤ a / D ∧ a / D ≤ (cI * xh) / (cJ * xr) := by
  constructor
  · exact div_nonneg ha (le_of_lt hD)
  · apply (div_le_div_iff hD (mul_pos hcJ hxr)).2
    calc
      a * (cJ * xr) = (cI * xh) * b := hex
      _ ≤ (cI * xh) * D :=
        mul_le_mul_of_nonneg_left hbD (mul_nonneg hcI hxh)

/-- A finite convex combination of bounded scalar templates is bounded. -/
theorem convex_template_bound (s : Finset ι) (pi phi : ι → ℝ) (M : ℝ)
    (hpi : ∀ i ∈ s, 0 ≤ pi i)
    (hsum : ∑ i in s, pi i = 1)
    (hphi : ∀ i ∈ s, |phi i| ≤ M) :
    |∑ i in s, pi i * phi i| ≤ M := by
  calc
    |∑ i in s, pi i * phi i| ≤ ∑ i in s, |pi i * phi i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i in s, pi i * |phi i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hpi i hi)]
    _ ≤ ∑ i in s, pi i * M := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hphi i hi) (hpi i hi)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- A finite template sum vanishes if every term has zero mass or zero template. -/
theorem annihilating_sum (s : Finset ι) (b phi : ι → ℝ)
    (hkill : ∀ i ∈ s, b i = 0 ∨ phi i = 0) :
    (∑ i in s, b i * phi i) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rcases hkill i hi with hb | hp
  · rw [hb, zero_mul]
  · rw [hp, mul_zero]

/-- A dominated coordinate cannot survive a zero source coordinate. -/
theorem dominated_zero (u v C : ℝ) (hdom : |v| ≤ C * |u|) (hu : u = 0) :
    v = 0 := by
  rw [hu, abs_zero, mul_zero] at hdom
  exact abs_eq_zero.mp (le_antisymm hdom (abs_nonneg v))

/-- Uniform scalar endpoint bound, including either termination branch. -/
theorem endpoint_bound (terminated : Prop) [Decidable terminated]
    (phi v M : ℝ) (hM : 0 ≤ M) (hphi : |phi| ≤ M) :
    |if terminated then 0 else phi * v| ≤ M * |v| := by
  split_ifs
  · simpa using mul_nonneg hM (abs_nonneg v)
  · rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hphi (abs_nonneg v)

/-- Explicit boundary estimate after the exchange masses are bounded.
    No sequence convergence or continuity is hidden in this statement. -/
theorem disappearing_template_bound (s : Finset ι) (pi phi R : ι → ℝ)
    (eps M : ℝ) (hM : 0 ≤ M)
    (hpi : ∀ i ∈ s, 0 ≤ pi i)
    (hphi : ∀ i ∈ s, |phi i| ≤ M)
    (hsmall : ∀ i ∈ s, pi i ≤ R i * eps) :
    |∑ i in s, pi i * phi i| ≤ M * (∑ i in s, R i) * eps := by
  calc
    |∑ i in s, pi i * phi i| ≤ ∑ i in s, |pi i * phi i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i in s, pi i * |phi i| := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (hpi i hi)]
    _ ≤ ∑ i in s, M * (R i * eps) := by
      apply Finset.sum_le_sum
      intro i hi
      calc
        pi i * |phi i| ≤ pi i * M :=
          mul_le_mul_of_nonneg_left (hphi i hi) (hpi i hi)
        _ ≤ (R i * eps) * M := mul_le_mul_of_nonneg_right (hsmall i hi) hM
        _ = M * (R i * eps) := mul_comm _ _
    _ = M * (∑ i in s, R i) * eps := by
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      ring

/-- If a set of sufficient size omits an active index, it contains an index
    outside the limiting support.  This covers both `s = p` and `s < p`. -/
theorem omitted_set_has_outside (I S : Finset ι) (r : ι)
    (hrS : r ∈ S) (hrI : r ∉ I) (hcard : S.card ≤ I.card) :
    ∃ h ∈ I, h ∉ S := by
  by_contra hnone
  push_neg at hnone
  have hsub : I ⊆ S.erase r := by
    intro i hi
    apply Finset.mem_erase.mpr
    constructor
    · intro hir
      subst i
      exact hrI hi
    · exact hnone i hi
  have hc := Finset.card_le_card hsub
  have he := Finset.card_erase_add_one hrS
  omega

/-- A single vanished coordinate forces its entire subset mass to vanish. -/
theorem mass_zero_of_member (I : Finset ι) (c : ℝ) (x : ι → ℝ)
    (h : ι) (hh : h ∈ I) (hx : x h = 0) : mass c x I = 0 := by
  unfold mass
  rw [Finset.prod_eq_zero hh hx, mul_zero]

/-- Exact algebraic annihilation on a support of size at most the subset size.
    The containing-index template vanishing is still supplied as a hypothesis. -/
theorem boundary_template_sum_zero (family : Finset (Finset ι))
    (S : Finset ι) (r : ι) (c phi : Finset ι → ℝ) (x : ι → ℝ)
    (hrS : r ∈ S)
    (hcard : ∀ I ∈ family, S.card ≤ I.card)
    (hzero : ∀ h, h ∉ S → x h = 0)
    (hphi : ∀ I ∈ family, r ∈ I → phi I = 0) :
    (∑ I in family, mass (c I) x I * phi I) = 0 := by
  apply annihilating_sum
  intro I hI
  by_cases hrI : r ∈ I
  · exact Or.inr (hphi I hI hrI)
  · obtain ⟨h, hhI, hhS⟩ := omitted_set_has_outside I S r hrS hrI (hcard I hI)
    exact Or.inl (mass_zero_of_member I (c I) x h hhI (hzero h hhS))

/-- The exchange probability bound instantiated with genuine finite products.
    The total is a finite sum and the replacement subset belongs to the family.
    Positivity of the total is explicit; no matrix theorem is concealed here. -/
theorem finite_product_probability_bound (family : Finset (Finset ι))
    (K : Finset ι) (h r : ι) (hh : h ∉ K) (hr : r ∉ K)
    (c : Finset ι → ℝ) (x : ι → ℝ)
    (hc : ∀ I, 0 < c I) (hx : ∀ i, 0 ≤ x i) (hxr : 0 < x r)
    (hJ : insert r K ∈ family)
    (hD : 0 < ∑ I in family, mass (c I) x I) :
    0 ≤ mass (c (insert h K)) x (insert h K) /
          (∑ I in family, mass (c I) x I) ∧
    mass (c (insert h K)) x (insert h K) /
          (∑ I in family, mass (c I) x I) ≤
        (c (insert h K) * x h) / (c (insert r K) * x r) := by
  have hm : ∀ I, 0 ≤ mass (c I) x I := by
    intro I
    exact mul_nonneg (le_of_lt (hc I)) (Finset.prod_nonneg (fun i _ => hx i))
  apply exchange_probability_bound
      (mass (c (insert h K)) x (insert h K))
      (mass (c (insert r K)) x (insert r K))
      (∑ I in family, mass (c I) x I)
      (c (insert h K)) (c (insert r K)) (x h) (x r)
  · exact hm _
  · exact hD
  · exact mass_le_total family (fun I => mass (c I) x I) (fun I _ => hm I) _ hJ
  · exact le_of_lt (hc _)
  · exact hc _
  · exact hx h
  · exact hxr
  · exact product_exchange_identity K h r hh hr _ _ x

#print axioms omitted_set_has_outside
#print axioms mass_zero_of_member
#print axioms boundary_template_sum_zero
#print axioms finite_product_probability_bound
#print axioms product_exchange_identity
#print axioms normalized_nonnegative
#print axioms normalized_sum_one
#print axioms mass_le_total
#print axioms exchange_probability_bound
#print axioms convex_template_bound
#print axioms annihilating_sum
#print axioms dominated_zero
#print axioms endpoint_bound
#print axioms disappearing_template_bound

end LMSDRankBoundary
