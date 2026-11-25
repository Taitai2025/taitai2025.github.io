import BB.TwoPointRates
import BB.TwoPointSmallStep

/-!
# Vanishing minimum of three consecutive two-dimensional BB1 ratios

The recurrence has a geometrically growing positive quadratic energy. Among
three consecutive log-state pairs, one pair lies far inside a common-sign
cone. The actual BB1 small-step estimate is then applied to that pair.

Nondegeneracy is explicit: both real components stay nonzero, and the initial
two logarithmic ratios are not both zero. No assertion is made about a quotient
with zero denominator after termination.
-/

noncomputable section
namespace BB
open Filter
open scoped Topology

/-- Both log-ratios have the same sign and absolute value at least L. -/
def sameSideLarge (L u v : ℝ) : Prop :=
  (L ≤ u ∧ L ≤ v) ∨ (u ≤ -L ∧ v ≤ -L)

lemma same_side_large_neg (L u v : ℝ) (h : sameSideLarge L (-u) (-v)) :
    sameSideLarge L u v := by
  rcases h with h | h
  · exact Or.inr ⟨by linarith [h.1], by linarith [h.2]⟩
  · exact Or.inl ⟨by linarith [h.1], by linarith [h.2]⟩

lemma three_pair_cone_nonneg (u v : ℝ) (hu : 0 ≤ u) :
    sameSideLarge ((|u|+|v|)/10) u v ∨
      sameSideLarge ((|u|+|v|)/10) v (v-2*u) ∨
      sameSideLarge ((|u|+|v|)/10) (v-2*u) (-v-2*u) := by
  rw [abs_of_nonneg hu]
  by_cases hvbig : u/2 ≤ v
  · have hv : 0 ≤ v := by linarith
    rw [abs_of_nonneg hv]
    by_cases hvsmall : v ≤ 4*u
    · exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
    · exact Or.inr (Or.inl (Or.inl ⟨by linarith, by linarith⟩))
  · by_cases hvneg : v ≤ -u/2
    · have hv : v ≤ 0 := by linarith
      rw [abs_of_nonpos hv]
      exact Or.inr (Or.inl (Or.inr ⟨by linarith, by linarith⟩))
    · apply Or.inr ∘ Or.inr ∘ Or.inr
      rcases le_total 0 v with hv | hv
      · rw [abs_of_nonneg hv]
        constructor <;> linarith
      · rw [abs_of_nonpos hv]
        constructor <;> linarith

/-- A fixed quantitative three-pair cone covering of the whole real plane. -/
theorem three_pair_cone (u v : ℝ) :
    sameSideLarge ((|u|+|v|)/10) u v ∨
      sameSideLarge ((|u|+|v|)/10) v (v-2*u) ∨
      sameSideLarge ((|u|+|v|)/10) (v-2*u) (-v-2*u) := by
  rcases le_total 0 u with hu | hu
  · exact three_pair_cone_nonneg u v hu
  · have h := three_pair_cone_nonneg (-u) (-v) (neg_nonneg.mpr hu)
    simp only [abs_neg] at h
    rcases h with h | h | h
    · exact Or.inl (same_side_large_neg _ _ _ h)
    · apply Or.inr ∘ Or.inl
      apply same_side_large_neg
      convert h using 1; ring
    · apply Or.inr ∘ Or.inr
      apply same_side_large_neg
      convert h using 1 <;> ring

def recurrenceThreshold (z : ℕ → ℝ) (n : ℕ) : ℝ := (|z n| + |z (n+1)|)/10

lemma recurrence_threshold_nonneg (z : ℕ → ℝ) (n : ℕ) : 0 ≤ recurrenceThreshold z n :=
  div_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) (by norm_num)

theorem recurrence_threshold_tendsto_atTop (z : ℕ → ℝ)
    (hz : ∀ n, z (n+2) = z (n+1)-2*z n) (hne : ¬ (z 0=0 ∧ z 1=0)) :
    Tendsto (recurrenceThreshold z) atTop atTop := by
  have he := recurrenceEnergy_tendsto_atTop z hz hne
  apply tendsto_atTop.2
  intro R
  by_cases hR : R ≤ 0
  · exact eventually_of_forall (fun n => hR.trans (recurrence_threshold_nonneg z n))
  · have hRpos : 0 < R := lt_of_not_ge hR
    filter_upwards [he.eventually (eventually_ge_atTop (3*(10*R)^2))] with n hn
    have hsum0 : 0 ≤ |z n|+|z (n+1)| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq : z (n+1)^2+z n^2 ≤ (|z n|+|z (n+1)|)^2 := by
      rw [← sq_abs (z (n+1)), ← sq_abs (z n)]
      nlinarith [mul_nonneg (abs_nonneg (z n)) (abs_nonneg (z (n+1)))]
    have hE := (recurrenceEnergy_bounds (z (n+1)) (z n)).2
    have hsquare : (10*R)^2 ≤ (|z n|+|z (n+1)|)^2 := by nlinarith
    have hsum : 10*R ≤ |z n|+|z (n+1)| := by
      by_contra hnot
      have hprod : 0 < (10*R-(|z n|+|z (n+1)|))*(10*R+(|z n|+|z (n+1)|)) :=
        mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) (by linarith only [hRpos, hsum0])
      nlinarith only [hsquare, hprod]
    dsimp [recurrenceThreshold]
    linarith

theorem recurrence_three_cone (z : ℕ → ℝ)
    (hz : ∀ n, z (n+2) = z (n+1)-2*z n) (n : ℕ) :
    sameSideLarge (recurrenceThreshold z n) (z n) (z (n+1)) ∨
      sameSideLarge (recurrenceThreshold z n) (z (n+1)) (z (n+2)) ∨
      sameSideLarge (recurrenceThreshold z n) (z (n+2)) (z (n+3)) := by
  have h3 : z (n+3) = -z (n+1)-2*z n := by
    calc
      _ = z (n+2)-2*z (n+1) := by simpa only [Nat.add_assoc] using hz (n+1)
      _ = _ := by rw [hz n]; ring
  rw [hz n,h3]
  exact three_pair_cone (z n) (z (n+1))

/-- The minimum of exactly the three ratios indexed n, n+1 and n+2. -/
def threeStepMinimum (p : ℕ → ℝ) (n : ℕ) : ℝ := min (p n) (min (p (n+1)) (p (n+2)))

theorem recurrence_three_minimum_tendsto_zero (z p : ℕ → ℝ)
    (hz : ∀ n, z (n+2) = z (n+1)-2*z n) (hne : ¬ (z 0=0 ∧ z 1=0))
    (hp : ∀ n, 0 ≤ p n) (F : ℝ → ℝ) (hF : Tendsto F atTop (𝓝 0))
    (hsmall : ∀ n L, 0 ≤ L → sameSideLarge L (z n) (z (n+1)) → p n ≤ F L) :
    Tendsto (threeStepMinimum p) atTop (𝓝 0) := by
  have hupp (n : ℕ) : threeStepMinimum p n ≤ F (recurrenceThreshold z n) := by
    rcases recurrence_three_cone z hz n with h | h | h
    · exact (min_le_left _ _).trans (hsmall n _ (recurrence_threshold_nonneg z n) h)
    · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
        (hsmall (n+1) _ (recurrence_threshold_nonneg z n) (by simpa only [Nat.add_assoc] using h))
    · exact ((min_le_right _ _).trans (min_le_right _ _)).trans
        (hsmall (n+2) _ (recurrence_threshold_nonneg z n) (by simpa only [Nat.add_assoc] using h))
  exact squeeze_zero (fun n => le_min (hp n) (le_min (hp (n+1)) (hp (n+2)))) hupp
    (hF.comp (recurrence_threshold_tendsto_atTop z hz hne))

lemma two_point_cone_bound_tendsto_zero (C : ℝ) :
    Tendsto (fun L : ℝ => Real.sqrt (C*(Real.exp (-L)+Real.exp (-2*L)))) atTop (𝓝 0) := by
  have h1 := Real.tendsto_exp_neg_atTop_nhds_zero
  have h2 : Tendsto (fun L : ℝ => Real.exp (-2*L)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Function.comp_apply, neg_mul] using h
  have h := (Real.continuous_sqrt.tendsto (C*(0+0))).comp ((h1.add h2).const_mul C)
  simpa only [zero_add, mul_zero, Real.sqrt_zero, Function.comp_apply] using h

lemma bb1_two_multipliers_ne_zero (a b xp yp : ℝ) (ha : 0 < a) (hab : a < b)
    (hxp : xp ≠ 0) (hyp : yp ≠ 0) :
    1-bb1Two a b xp yp*a ≠ 0 ∧ 1-bb1Two a b xp yp*b ≠ 0 := by
  have hp : 0 < xp^2 := sq_pos_of_ne_zero hxp
  have hq : 0 < yp^2 := sq_pos_of_ne_zero hyp
  have hd : a*xp^2+b*yp^2 ≠ 0 := (add_pos (mul_pos ha hp) (mul_pos (ha.trans hab) hq)).ne'
  constructor
  · have heq : 1-bb1Two a b xp yp*a = (b-a)*yp^2/(a*xp^2+b*yp^2) := by
      unfold bb1Two
      field_simp [hd]
      ring
    rw [heq]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.ne') (pow_ne_zero 2 hyp)) hd
  · have heq : 1-bb1Two a b xp yp*b = (a-b)*xp^2/(a*xp^2+b*yp^2) := by
      unfold bb1Two
      field_simp [hd]
      ring
    rw [heq]
    exact div_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.ne) (pow_ne_zero 2 hxp)) hd

/-- A matched two-point orbit with both initial components nonzero never
loses either component. Thus the nondegeneracy premises of the limit theorem
follow from the actual matched initialization. -/
theorem matched_two_point_components_nonzero (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0)
    (hx1 : x 1 = (1-bb1Two a b (x 0) (y 0)*a)*x 0)
    (hy1 : y 1 = (1-bb1Two a b (x 0) (y 0)*b)*y 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1)) :
    ∀ n, x n ≠ 0 ∧ y n ≠ 0 := by
  have hfirst : x 1 ≠ 0 ∧ y 1 ≠ 0 := by
    rw [hx1,hy1]
    have hm := bb1_two_multipliers_ne_zero a b (x 0) (y 0) ha hab hx0 hy0
    exact ⟨mul_ne_zero hm.1 hx0,mul_ne_zero hm.2 hy0⟩
  intro n
  exact @Nat.twoStepInduction (fun n => x n ≠ 0 ∧ y n ≠ 0) ⟨hx0,hy0⟩ hfirst
    (fun k hk hk1 => by
      have hm := bb1_two_multipliers_ne_zero a b (x k) (y k) ha hab hk.1 hk.2
      change x (k+2) ≠ 0 ∧ y (k+2) ≠ 0
      rw [hxu k,hyu k]
      exact ⟨mul_ne_zero hm.1 hk1.1,mul_ne_zero hm.2 hk1.2⟩) n

/-- The actual one-step Euclidean norm ratio of a real component trajectory. -/
def twoPointNormRatio (x y : ℕ → ℝ) (n : ℕ) : ℝ :=
  normTwo (x (n+1)) (y (n+1))/normTwo (x n) (y n)

/-- The displayed Dai three-step assertion for every nondegenerate actual
two-component BB1 trajectory, with arbitrary first gradient pair. -/
theorem bb1_two_min_three_norm_ratio (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx : ∀ n, x n ≠ 0) (hy : ∀ n, y n ≠ 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1))
    (hne : ratioTwo (x 0) (y 0) ≠ 1 ∨ ratioTwo (x 1) (y 1) ≠ 1) :
    Tendsto (threeStepMinimum (twoPointNormRatio x y)) atTop (𝓝 0) := by
  let z : ℕ → ℝ := fun n => Real.log (ratioTwo (x n) (y n))
  have hzpos (n : ℕ) : 0 < ratioTwo (x n) (y n) :=
    div_pos (sq_pos_of_ne_zero (hx n)) (sq_pos_of_ne_zero (hy n))
  have hrec : ∀ n, z (n+2) = z (n+1)-2*z n :=
    positive_ratio_log_recurrence _ hzpos (bb1_two_orbit_ratio_recurrence ha hab x y hx hy hxu hyu)
  have hzinit : ¬ (z 0 = 0 ∧ z 1 = 0) := by
    rintro ⟨h0,h1⟩
    have he0 := congrArg Real.exp h0
    have he1 := congrArg Real.exp h1
    change Real.exp (Real.log (ratioTwo (x 0) (y 0))) = Real.exp 0 at he0
    change Real.exp (Real.log (ratioTwo (x 1) (y 1))) = Real.exp 0 at he1
    rw [Real.exp_log (hzpos 0),Real.exp_zero] at he0
    rw [Real.exp_log (hzpos 1),Real.exp_zero] at he1
    rcases hne with h | h
    · exact h he0
    · exact h he1
  have hp (n : ℕ) : 0 ≤ twoPointNormRatio x y (n+1) :=
    div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsmall (n : ℕ) (L : ℝ) (_hL : 0 ≤ L)
      (hcone : sameSideLarge L (z n) (z (n+1))) :
      twoPointNormRatio x y (n+1) ≤
        Real.sqrt (((b-a)/a)^2*(Real.exp (-L)+Real.exp (-2*L))) := by
    simpa only [twoPointNormRatio,Nat.add_assoc] using
      bb1_two_norm_ratio_le_of_log_cone a b ha hab x y n L
        (hx n) (hy n) (hx (n+1)) (hy (n+1)) (hxu n) (hyu n) hcone
  have ht := recurrence_three_minimum_tendsto_zero z (fun n => twoPointNormRatio x y (n+1))
    hrec hzinit hp _ (two_point_cone_bound_tendsto_zero (((b-a)/a)^2)) hsmall
  apply (tendsto_add_atTop_iff_nat 1).mp
  simpa only [threeStepMinimum,Nat.add_assoc,Nat.add_comm 1 2] using ht

/-- Matched nonbalance is a direct corollary: nonzero components thereafter
are proved, rather than assumed. -/
theorem matched_bb1_two_min_three_norm_ratio (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0)
    (hbalance : (x 0)^2 ≠ (y 0)^2)
    (hx1 : x 1 = (1-bb1Two a b (x 0) (y 0)*a)*x 0)
    (hy1 : y 1 = (1-bb1Two a b (x 0) (y 0)*b)*y 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1)) :
    Tendsto (threeStepMinimum (twoPointNormRatio x y)) atTop (𝓝 0) := by
  have hxy := matched_two_point_components_nonzero a b ha hab x y hx0 hy0 hx1 hy1 hxu hyu
  apply bb1_two_min_three_norm_ratio a b ha hab x y (fun n => (hxy n).1) (fun n => (hxy n).2) hxu hyu
  apply Or.inl
  intro h
  exact hbalance ((div_eq_one_iff_eq (pow_ne_zero 2 hy0)).mp h)

/-- An eventual contraction every three steps gives an exponential envelope
at every index, with the finitely many initial values absorbed into one C. -/
theorem envelope_of_eventual_three_step (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (γ : ℝ) (hγ : 0 < γ) (hstep : ∀ᶠ n in atTop, f (n+3) ≤ γ^3*f n) :
    ExponentialEnvelope f γ := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp hstep
  let C : ℝ := 1 + ∑ i ∈ Finset.range (N+3), f i/γ^i
  have hs0 : 0 ≤ ∑ i ∈ Finset.range (N+3), f i/γ^i :=
    Finset.sum_nonneg (fun i _ => div_nonneg (hf i) (pow_pos hγ i).le)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < N+3
    · have ht : f n/γ^n ≤ ∑ i ∈ Finset.range (N+3), f i/γ^i :=
        Finset.single_le_sum (fun i _ => div_nonneg (hf i) (pow_pos hγ i).le)
          (Finset.mem_range.mpr hn)
      have htC : f n/γ^n ≤ C := by dsimp [C]; linarith
      exact (div_le_iff (pow_pos hγ n)).mp htC
    · have hm : N ≤ n-3 := by omega
      have hmn : n-3 < n := by omega
      have he : n-3+3 = n := by omega
      calc
        f n = f (n-3+3) := by rw [he]
        _ ≤ γ^3*f (n-3) := hN _ hm
        _ ≤ γ^3*(C*γ^(n-3)) := mul_le_mul_of_nonneg_left (ih _ hmn) (pow_pos hγ 3).le
        _ = C*(γ^(n-3)*γ^3) := by ring
        _ = C*γ^(n-3+3) := by rw [pow_add]
        _ = C*γ^n := by rw [he]

lemma triple_product_le_minimum (p q r D : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hD : 0 ≤ D) (hpD : p ≤ D) (hqD : q ≤ D) (hrD : r ≤ D) :
    p*q*r ≤ D^2*min p (min q r) := by
  rw [mul_min_of_nonneg _ _ (sq_nonneg D),mul_min_of_nonneg _ _ (sq_nonneg D)]
  have h0 : p*q*r ≤ D^2*p := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hqD hrD hr hD) hp
    nlinarith only [h]
  have h1 : p*q*r ≤ D^2*q := by
    have h := mul_le_mul_of_nonneg_left (mul_le_mul hpD hrD hr hD) hq
    nlinarith only [h]
  have h2 : p*q*r ≤ D^2*r := by
    have h := mul_le_mul_of_nonneg_right (mul_le_mul hpD hqD hq hD) hr
    nlinarith only [h]
  exact le_min h0 (le_min h1 h2)

/-- A bounded sequence of positive one-step ratios whose three-step minima
vanish has zero asymptotic root factor, i.e. R-superlinear convergence. -/
theorem rootFactor_zero_of_three_minimum (f : ℕ → ℝ) (hf : ∀ n, 0 < f n)
    (D : ℝ) (hD : 0 < D) (hbound : ∀ n, f (n+1)/f n ≤ D)
    (hmin : Tendsto (threeStepMinimum (fun n => f (n+1)/f n)) atTop (𝓝 0)) :
    rootFactor (fun n => f n/f 0) = 0 := by
  have henv (γ : ℝ) (hγ : 0 < γ) : ExponentialEnvelope f γ := by
    apply envelope_of_eventual_three_step f (fun n => (hf n).le) γ hγ
    have he := (tendsto_order.mp hmin).2 (γ^3/D^2) (by positivity)
    filter_upwards [he] with n hn
    have hprod := triple_product_le_minimum (f (n+1)/f n) (f (n+2)/f (n+1))
      (f (n+3)/f (n+2)) D (div_pos (hf _) (hf _)).le (div_pos (hf _) (hf _)).le
      (div_pos (hf _) (hf _)).le hD.le (hbound n)
      (by simpa only [Nat.add_assoc] using hbound (n+1))
      (by simpa only [Nat.add_assoc] using hbound (n+2))
    have hsmall : D^2 * threeStepMinimum (fun n => f (n+1)/f n) n ≤ γ^3 := by
      have h := (le_div_iff (sq_pos_of_pos hD)).mp hn.le
      simpa only [mul_comm] using h
    have hprod' : (f (n+1)/f n)*(f (n+2)/f (n+1))*(f (n+3)/f (n+2)) ≤ γ^3 := by
      apply hprod.trans
      simpa only [threeStepMinimum,Nat.add_assoc] using hsmall
    have htel : (f (n+1)/f n)*(f (n+2)/f (n+1))*(f (n+3)/f (n+2))*f n = f (n+3) := by
      field_simp [(hf n).ne',(hf (n+1)).ne',(hf (n+2)).ne']
      ring
    rw [← htel]
    exact mul_le_mul_of_nonneg_right hprod' (hf n).le
  obtain ⟨C,hC,hCenv⟩ := henv 1 zero_lt_one
  have hbounded := rootTerm_bounded_of_eventual_envelope f (fun n => (hf n).le) C 1
    hC zero_le_one (eventually_of_forall hCenv)
  rw [rootFactor_div_const f (fun n => (hf n).le) hbounded (f 0) (hf 0)]
  apply le_antisymm
  · exact rootFactor_le_of_all_envelopes f (fun n => (hf n).le) 0 le_rfl henv
  · exact rootFactor_nonneg f (fun n => (hf n).le) hbounded

/-- In the nondegenerate, nonbalanced two-dimensional case the actual BB1
trajectory is R-superlinear: its normalized norm root factor is zero. -/
theorem bb1_two_norm_rootFactor_eq_zero (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx : ∀ n, x n ≠ 0) (hy : ∀ n, y n ≠ 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1))
    (hne : ratioTwo (x 0) (y 0) ≠ 1 ∨ ratioTwo (x 1) (y 1) ≠ 1) :
    rootFactor (fun n => normTwo (x n) (y n)/normTwo (x 0) (y 0)) = 0 := by
  have hf (n : ℕ) : 0 < normTwo (x n) (y n) :=
    Real.sqrt_pos.2 (add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (hx n)) (sq_nonneg _))
  have hbase : 0 ≤ twoPointNormRatio x y 0 := div_nonneg (hf 1).le (hf 0).le
  have hδ : 0 < (b-a)/a := div_pos (sub_pos.mpr hab) ha
  let D : ℝ := 1+twoPointNormRatio x y 0+(b-a)/a
  have hD : 0 < D := by dsimp [D]; linarith
  have hbound (n : ℕ) : normTwo (x (n+1)) (y (n+1))/normTwo (x n) (y n) ≤ D := by
    cases n with
    | zero => change twoPointNormRatio x y 0 ≤ D; dsimp [D]; linarith
    | succ k =>
      calc
        _ ≤ (b-a)/a := by
          simpa only [Nat.succ_eq_add_one,Nat.add_assoc] using
            bb1_two_norm_ratio_le a b ha hab x y k
              (hx k) (hy k) (hx (k+1)) (hy (k+1)) (hxu k) (hyu k)
        _ ≤ D := by dsimp [D]; linarith
  exact rootFactor_zero_of_three_minimum (fun n => normTwo (x n) (y n)) hf D hD hbound
    (bb1_two_min_three_norm_ratio a b ha hab x y hx hy hxu hyu hne)

/-- The matched nonbalanced case has zero root factor with no nonvanishing
premise on future iterates. -/
theorem matched_bb1_two_norm_rootFactor_eq_zero (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx0 : x 0 ≠ 0) (hy0 : y 0 ≠ 0)
    (hbalance : (x 0)^2 ≠ (y 0)^2)
    (hx1 : x 1 = (1-bb1Two a b (x 0) (y 0)*a)*x 0)
    (hy1 : y 1 = (1-bb1Two a b (x 0) (y 0)*b)*y 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1)) :
    rootFactor (fun n => normTwo (x n) (y n)/normTwo (x 0) (y 0)) = 0 := by
  have hxy := matched_two_point_components_nonzero a b ha hab x y hx0 hy0 hx1 hy1 hxu hyu
  apply bb1_two_norm_rootFactor_eq_zero a b ha hab x y (fun n => (hxy n).1) (fun n => (hxy n).2) hxu hyu
  apply Or.inl
  intro h
  exact hbalance ((div_eq_one_iff_eq (pow_ne_zero 2 hy0)).mp h)

end BB
