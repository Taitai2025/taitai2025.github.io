import BB.HilbertExample
import BB.LinearCoordinates
import BB.Asymptotics
import BB.UniversalWeighted
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual continuous-spectrum multiplication example

The Hilbert space is `L²(ℝ, volume.restrict (Icc a b))`, the standard realization
of `L²([a,b])`. The bounded operator multiplies by the spectral coordinate.
The trajectory is the equivalence class of `(1 - 2*t/(a+b))^n`.
-/

namespace BB
noncomputable section
open MeasureTheory Filter
open scoped Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

abbrev intervalL2 (a b : ℝ) := Lp ℝ 2 (volume.restrict (Set.Icc a b))

lemma interval_coordinate_mul_mem (a b : ℝ) (g : intervalL2 a b) :
    Memℒp (fun t : ℝ => t * g t) 2 (volume.restrict (Set.Icc a b)) := by
  apply (Lp.memℒp g).of_le_mul (c := max |a| |b|)
    (continuous_id.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change ‖t * g t‖ ≤ max |a| |b| * ‖g t‖
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_le_max_abs_abs ht.1 ht.2) (norm_nonneg _)

def intervalMultiplicationLinear (a b : ℝ) : intervalL2 a b →ₗ[ℝ] intervalL2 a b where
  toFun g := (interval_coordinate_mul_mem a b g).toLp (fun t => t * g t)
  map_add' g h := by
    apply Lp.ext
    filter_upwards [(interval_coordinate_mul_mem a b (g + h)).coeFn_toLp,
      (interval_coordinate_mul_mem a b g).coeFn_toLp,
      (interval_coordinate_mul_mem a b h).coeFn_toLp,
      Lp.coeFn_add g h,
      Lp.coeFn_add ((interval_coordinate_mul_mem a b g).toLp _)
        ((interval_coordinate_mul_mem a b h).toLp _)] with t h1 h2 h3 h4 h5
    rw [h1, h5]
    simp only [Pi.add_apply]
    rw [h2, h3, h4]
    exact mul_add _ _ _
  map_smul' r g := by
    apply Lp.ext
    filter_upwards [(interval_coordinate_mul_mem a b (r • g)).coeFn_toLp,
      (interval_coordinate_mul_mem a b g).coeFn_toLp,
      Lp.coeFn_smul r g,
      Lp.coeFn_smul r ((interval_coordinate_mul_mem a b g).toLp _)]
        with t h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h1, h4]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h2, h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

lemma interval_multiplication_coe (a b : ℝ) (g : intervalL2 a b) :
    ⇑(intervalMultiplicationLinear a b g) =ᵐ[volume.restrict (Set.Icc a b)]
      fun t => t * g t := (interval_coordinate_mul_mem a b g).coeFn_toLp

lemma interval_multiplication_norm_le (a b : ℝ) (g : intervalL2 a b) :
    ‖intervalMultiplicationLinear a b g‖ ≤ max |a| |b| * ‖g‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [interval_multiplication_coe a b g,
    ae_restrict_mem measurableSet_Icc] with t hg ht
  rw [hg, norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (abs_le_max_abs_abs ht.1 ht.2) (norm_nonneg _)

def intervalMultiplication (a b : ℝ) : intervalL2 a b →L[ℝ] intervalL2 a b :=
  (intervalMultiplicationLinear a b).mkContinuous (max |a| |b|)
    (interval_multiplication_norm_le a b)

lemma interval_multiplication_symmetric (a b : ℝ) :
    (intervalMultiplication a b).toLinearMap.IsSymmetric := by
  intro g h
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [interval_multiplication_coe a b g,
    interval_multiplication_coe a b h] with t hg hh
  change (intervalMultiplicationLinear a b g) t * h t =
    g t * (intervalMultiplicationLinear a b h) t
  rw [hg, hh]
  ring

lemma interval_l2_norm_sq_integral (a b : ℝ) (g : intervalL2 a b) :
    ‖g‖^2 = ∫ t in Set.Icc a b, (g t)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact ae_of_all _ (fun _ => by simp only [real_inner_comm, mul_comm, RCLike.inner_apply,
    conj_trivial, pow_two])

lemma interval_multiplication_inner (a b : ℝ) (g : intervalL2 a b) :
    ⟪g, intervalMultiplication a b g⟫ = ∫ t in Set.Icc a b, t*(g t)^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [interval_multiplication_coe a b g] with t ht
  change g t * intervalMultiplicationLinear a b g t = _
  rw [ht]
  ring

lemma interval_multiplication_form_bounds (a b : ℝ) (g : intervalL2 a b) :
    a*‖g‖^2 ≤ ⟪g, intervalMultiplication a b g⟫ ∧
    ⟪g, intervalMultiplication a b g⟫ ≤ b*‖g‖^2 := by
  have hg : Integrable (fun t : ℝ => (g t)^2) (volume.restrict (Set.Icc a b)) :=
    (Lp.memℒp g).integrable_sq
  have hAg : Integrable (fun t : ℝ => t*(g t)^2) (volume.restrict (Set.Icc a b)) := by
    apply (L2.integrable_inner (𝕜 := ℝ) g (intervalMultiplication a b g)).congr
    filter_upwards [interval_multiplication_coe a b g] with t ht
    change g t * intervalMultiplicationLinear a b g t = _
    rw [ht]
    ring
  rw [interval_l2_norm_sq_integral, interval_multiplication_inner,
    ← integral_mul_left, ← integral_mul_left]
  constructor
  · apply integral_mono_ae (hg.const_mul a) hAg
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right ht.1 (sq_nonneg _)
  · apply integral_mono_ae hAg (hg.const_mul b)
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact mul_le_mul_of_nonneg_right ht.2 (sq_nonneg _)

lemma interval_continuous_mem (a b : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    Memℒp f 2 (volume.restrict (Set.Icc a b)) := by
  apply (memℒp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
  exact (hf.pow 2).continuousOn.integrableOn_Icc

def intervalL2Continuous (a b : ℝ) (f : ℝ → ℝ) (hf : Continuous f) : intervalL2 a b :=
  (interval_continuous_mem a b f hf).toLp f

lemma interval_l2_continuous_coe (a b : ℝ) (f : ℝ → ℝ) (hf : Continuous f) :
    ⇑(intervalL2Continuous a b f hf) =ᵐ[volume.restrict (Set.Icc a b)] f :=
  (interval_continuous_mem a b f hf).coeFn_toLp

lemma interval_l2_continuous_norm_sq (a b : ℝ) (hab : a ≤ b)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ‖intervalL2Continuous a b f hf‖^2 = ∫ t in a..b, (f t)^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [interval_l2_continuous_coe a b f hf] with t ht
  change (intervalL2Continuous a b f hf t) * (intervalL2Continuous a b f hf t) = _
  rw [ht, pow_two]

def intervalPolynomial (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  (1 - 2 * t / (a + b))^n

lemma interval_polynomial_continuous (a b : ℝ) (n : ℕ) :
    Continuous (intervalPolynomial a b n) := by
  unfold intervalPolynomial
  exact (continuous_const.sub ((continuous_const.mul continuous_id).div_const (a+b))).pow n

def intervalTrajectory (a b : ℝ) (n : ℕ) : intervalL2 a b :=
  intervalL2Continuous a b (intervalPolynomial a b n)
    (interval_polynomial_continuous a b n)

lemma interval_trajectory_coe (a b : ℝ) (n : ℕ) :
    ⇑(intervalTrajectory a b n) =ᵐ[volume.restrict (Set.Icc a b)]
      intervalPolynomial a b n :=
  interval_l2_continuous_coe a b _ _

lemma interval_polynomial_affine (a b : ℝ) (hsum : a + b ≠ 0) (n : ℕ) (t : ℝ) :
    intervalPolynomial a b n ((b-a)/2*t+(a+b)/2) = (-rate a b*t)^n := by
  unfold intervalPolynomial
  congr 1
  unfold rate
  have hsum' : b+a ≠ 0 := by simpa only [add_comm] using hsum
  field_simp [hsum, hsum']
  ring

lemma interval_polynomial_norm_integral (a b : ℝ) (hsum : a + b ≠ 0) (n : ℕ) :
    (∫ t in a..b, (intervalPolynomial a b n t)^2) =
      (b-a) * (rate a b)^(2*n) / (2*(n:ℝ)+1) := by
  have h := intervalIntegral.mul_integral_comp_mul_add
    (f := fun t => (intervalPolynomial a b n t)^2) ((b-a)/2) ((a+b)/2)
    (a := (-1:ℝ)) (b := 1)
  have hl : (b-a)/2*(-1)+(a+b)/2=a := by ring
  have hr : (b-a)/2*1+(a+b)/2=b := by ring
  rw [hl, hr] at h
  simp_rw [interval_polynomial_affine a b hsum n] at h
  rw [continuous_spectrum_norm_square] at h
  rw [← h]
  ring

lemma interval_trajectory_norm_sq (a b : ℝ) (hab : a ≤ b) (hsum : a + b ≠ 0)
    (n : ℕ) :
    ‖intervalTrajectory a b n‖^2 =
      (b-a) * (rate a b)^(2*n) / (2*(n:ℝ)+1) := by
  unfold intervalTrajectory
  rw [interval_l2_continuous_norm_sq a b hab, interval_polynomial_norm_integral a b hsum]

lemma interval_polynomial_centered_integral (a b : ℝ) (hsum : a + b ≠ 0) (n : ℕ) :
    (∫ t in a..b, (t-(a+b)/2) * (intervalPolynomial a b n t)^2) = 0 := by
  have h := intervalIntegral.mul_integral_comp_mul_add
    (f := fun t => (t-(a+b)/2) * (intervalPolynomial a b n t)^2)
    ((b-a)/2) ((a+b)/2) (a := (-1:ℝ)) (b := 1)
  have hl : (b-a)/2*(-1)+(a+b)/2=a := by ring
  have hr : (b-a)/2*1+(a+b)/2=b := by ring
  rw [hl, hr] at h
  simp_rw [interval_polynomial_affine a b hsum n, add_sub_cancel_right] at h
  have hp : (fun t : ℝ => (b-a)/2*t*((-rate a b*t)^n)^2) =
      (fun t : ℝ => (b-a)/2 * (t*((-rate a b*t)^n)^2)) := by
    funext t
    ring
  rw [hp, intervalIntegral.integral_const_mul, continuous_spectrum_centered_moment,
    mul_zero, mul_zero] at h
  exact h.symm

lemma interval_trajectory_inner (a b : ℝ) (hab : a ≤ b) (hsum : a + b ≠ 0) (n : ℕ) :
    ⟪intervalTrajectory a b n, intervalMultiplication a b (intervalTrajectory a b n)⟫ =
      (a+b)/2 * ‖intervalTrajectory a b n‖^2 := by
  have hinner :
      ⟪intervalTrajectory a b n, intervalMultiplication a b (intervalTrajectory a b n)⟫ =
        ∫ t in a..b, t * (intervalPolynomial a b n t)^2 := by
    rw [L2.inner_def, intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [interval_trajectory_coe a b n,
      interval_multiplication_coe a b (intervalTrajectory a b n)] with t ht hAt
    change (intervalTrajectory a b n t) *
      (intervalMultiplicationLinear a b (intervalTrajectory a b n) t) = _
    rw [hAt, ht]
    ring
  rw [hinner]
  have hp : (fun t : ℝ => t * (intervalPolynomial a b n t)^2) =
      fun t => (a+b)/2 * (intervalPolynomial a b n t)^2 +
        (t-(a+b)/2) * (intervalPolynomial a b n t)^2 := by
    funext t
    ring
  have hc := interval_polynomial_continuous a b n
  have hf : IntervalIntegrable (fun t => (a+b)/2 * (intervalPolynomial a b n t)^2)
      volume a b := (continuous_const.mul (hc.pow 2)).intervalIntegrable a b
  have hg : IntervalIntegrable (fun t => (t-(a+b)/2) * (intervalPolynomial a b n t)^2)
      volume a b := ((continuous_id.sub continuous_const).mul (hc.pow 2)).intervalIntegrable a b
  rw [hp, intervalIntegral.integral_add hf hg,
    intervalIntegral.integral_const_mul, interval_polynomial_centered_integral a b hsum,
    add_zero]
  congr 1
  exact (interval_l2_continuous_norm_sq a b hab _ hc).symm

lemma interval_trajectory_norm_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    0 < ‖intervalTrajectory a b n‖ := by
  have hsum : a+b ≠ 0 := ne_of_gt (by linarith)
  have hsq := interval_trajectory_norm_sq a b hab.le hsum n
  have hr : 0 < (b-a) * (rate a b)^(2*n) / (2*(n:ℝ)+1) := by
    exact div_pos (mul_pos (sub_pos.mpr hab) (pow_pos (rate_pos ha hab) _)) (by positivity)
  nlinarith [norm_nonneg (intervalTrajectory a b n)]

lemma interval_trajectory_bb1 (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    operatorBB1 (intervalMultiplication a b).toLinearMap (intervalTrajectory a b n) =
      2 / (a+b) := by
  unfold operatorBB1
  change ‖intervalTrajectory a b n‖^2 /
    ⟪intervalTrajectory a b n, intervalMultiplication a b (intervalTrajectory a b n)⟫ = _
  rw [interval_trajectory_inner a b hab.le (ne_of_gt (by linarith))]
  have hn := (interval_trajectory_norm_pos a b ha hab n).ne'
  have hs : a+b ≠ 0 := ne_of_gt (by linarith)
  field_simp
  ring

lemma interval_trajectory_step (a b : ℝ) (n : ℕ) :
    intervalTrajectory a b (n+1) = operatorGradientStep
      (intervalMultiplication a b).toLinearMap (2/(a+b)) (intervalTrajectory a b n) := by
  apply Lp.ext
  have hsub := Lp.coeFn_sub (intervalTrajectory a b n)
    ((2/(a+b)) • intervalMultiplication a b (intervalTrajectory a b n))
  filter_upwards [interval_trajectory_coe a b (n+1), interval_trajectory_coe a b n,
    interval_multiplication_coe a b (intervalTrajectory a b n), hsub,
    Lp.coeFn_smul (2/(a+b)) (intervalMultiplication a b (intervalTrajectory a b n))]
      with t h1 h2 h3 h4 h5
  change intervalTrajectory a b (n+1) t =
    (intervalTrajectory a b n - (2/(a+b)) • intervalMultiplication a b
      (intervalTrajectory a b n)) t
  rw [h1, h4, Pi.sub_apply, h5, Pi.smul_apply, smul_eq_mul]
  change intervalPolynomial a b (n+1) t =
    intervalTrajectory a b n t - (2/(a+b)) *
      intervalMultiplicationLinear a b (intervalTrajectory a b n) t
  rw [h3, h2]
  simp only [intervalPolynomial, pow_succ]
  ring

lemma interval_trajectory_matched_bb1 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    intervalTrajectory a b 1 = operatorGradientStep
      (intervalMultiplication a b).toLinearMap
      (operatorBB1 (intervalMultiplication a b).toLinearMap (intervalTrajectory a b 0))
      (intervalTrajectory a b 0) ∧
    ∀ n, intervalTrajectory a b (n+2) = operatorGradientStep
      (intervalMultiplication a b).toLinearMap
      (operatorBB1 (intervalMultiplication a b).toLinearMap (intervalTrajectory a b n))
      (intervalTrajectory a b (n+1)) := by
  constructor
  · rw [interval_trajectory_bb1 a b ha hab]
    exact interval_trajectory_step a b 0
  · intro n
    rw [interval_trajectory_bb1 a b ha hab]
    exact interval_trajectory_step a b (n+1)

lemma interval_trajectory_norm (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    ‖intervalTrajectory a b n‖ =
      Real.sqrt (b-a) * (rate a b)^n / Real.sqrt (2*(n:ℝ)+1) := by
  have hs := interval_trajectory_norm_sq a b hab.le (ne_of_gt (by linarith)) n
  have hd : 0 < 2*(n:ℝ)+1 := by positivity
  have hw := Real.sq_sqrt (sub_nonneg.mpr hab.le)
  have he := Real.sq_sqrt hd.le
  have hp : 0 ≤ Real.sqrt (b-a) * (rate a b)^n / Real.sqrt (2*(n:ℝ)+1) := by
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (rate_pos ha hab).le _))
      (Real.sqrt_nonneg _)
  have hsq : (Real.sqrt (b-a) * (rate a b)^n / Real.sqrt (2*(n:ℝ)+1))^2 =
      (b-a)*(rate a b)^(2*n)/(2*(n:ℝ)+1) := by
    rw [div_pow, mul_pow, hw, he]
    rw [← pow_mul, Nat.mul_comm n 2]
  nlinarith [norm_nonneg (intervalTrajectory a b n)]

lemma interval_trajectory_normalized_norm (a b : ℝ) (ha : 0 < a) (hab : a < b)
    (n : ℕ) :
    ‖intervalTrajectory a b n‖ / ‖intervalTrajectory a b 0‖ =
      (rate a b)^n / Real.sqrt (2*(n:ℝ)+1) := by
  rw [interval_trajectory_norm a b ha hab n, interval_trajectory_norm a b ha hab 0]
  simp only [pow_zero, Nat.cast_zero, mul_zero, zero_add, Real.sqrt_one, mul_one, div_one]
  have hw : Real.sqrt (b-a) ≠ 0 := (Real.sqrt_pos.mpr (sub_pos.mpr hab)).ne'
  field_simp
  ring

lemma interval_trajectory_root_limit (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto (rootTerm (fun n => ‖intervalTrajectory a b n‖ / ‖intervalTrajectory a b 0‖))
      atTop (𝓝 (rate a b)) := by
  have he : (fun n => ‖intervalTrajectory a b n‖ / ‖intervalTrajectory a b 0‖) =
      (fun n : ℕ => (rate a b)^n / Real.sqrt (2*(n:ℝ)+1)) := by
    funext n
    exact interval_trajectory_normalized_norm a b ha hab n
  rw [he]
  exact continuous_spectrum_norm_root_limit (rate a b) (rate_pos ha hab).le

lemma interval_trajectory_rootFactor (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    rootFactor (fun n => ‖intervalTrajectory a b n‖ / ‖intervalTrajectory a b 0‖) =
      rate a b := (interval_trajectory_root_limit a b ha hab).limsup_eq

lemma interval_trajectory_root_bounded (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    atTop.IsBoundedUnder (· ≤ ·) (rootTerm (fun n => ‖intervalTrajectory a b n‖)) := by
  apply rootTerm_bounded_of_comparison
    (fun n => ‖intervalTrajectory a b n‖)
    (fun n => ‖intervalTrajectory a b n‖ / ‖intervalTrajectory a b 0‖)
    (fun _ => norm_nonneg _)
    (fun _ => div_nonneg (norm_nonneg _) (norm_nonneg _))
    (interval_trajectory_root_limit a b ha hab).isBoundedUnder_le
    ‖intervalTrajectory a b 0‖ (interval_trajectory_norm_pos a b ha hab 0)
  apply eventually_of_forall
  intro n
  rw [mul_div_cancel₀ _ (interval_trajectory_norm_pos a b ha hab 0).ne']

lemma interval_multiplication_no_eigenvectors (a b ell : ℝ) (g : intervalL2 a b)
    (h : intervalMultiplication a b g = ell • g) : g = 0 := by
  have hne : ∀ᵐ t : ℝ ∂volume.restrict (Set.Icc a b), t ≠ ell := by
    apply ae_restrict_of_ae
    exact (Set.countable_singleton ell).ae_not_mem volume
  apply Lp.ext
  filter_upwards [interval_multiplication_coe a b g, Lp.coeFn_smul ell g,
    Lp.coeFn_zero ℝ 2 (volume.restrict (Set.Icc a b)), hne] with t ht hs hz hneq
  have he : t * g t = ell * g t := by
    calc
      t * g t = intervalMultiplication a b g t := ht.symm
      _ = (ell • g) t := congrArg (fun f : intervalL2 a b => f t) h
      _ = ell * g t := hs
  rw [hz]
  exact (mul_eq_mul_right_iff.mp he).resolve_left hneq

lemma interval_continuousOn_mem (a b : ℝ) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc a b)) :
    Memℒp f 2 (volume.restrict (Set.Icc a b)) := by
  apply (memℒp_two_iff_integrable_sq
    (hf.aestronglyMeasurable_of_isCompact isCompact_Icc measurableSet_Icc)).mpr
  exact (hf.pow 2).integrableOn_Icc

def intervalWeightedPolynomial (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  intervalPolynomial a b n t / Real.sqrt t

lemma interval_weighted_polynomial_continuousOn (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ContinuousOn (intervalWeightedPolynomial a b n) (Set.Icc a b) := by
  exact (interval_polynomial_continuous a b n).continuousOn.div
    Real.continuous_sqrt.continuousOn (fun t ht => (Real.sqrt_pos.mpr (ha.trans_le ht.1)).ne')

def intervalWeightedTrajectory (a b : ℝ) (ha : 0 < a) (n : ℕ) : intervalL2 a b :=
  (interval_continuousOn_mem a b (intervalWeightedPolynomial a b n)
    (interval_weighted_polynomial_continuousOn a b ha n)).toLp (intervalWeightedPolynomial a b n)

lemma interval_weighted_trajectory_coe (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ⇑(intervalWeightedTrajectory a b ha n) =ᵐ[volume.restrict (Set.Icc a b)]
      intervalWeightedPolynomial a b n :=
  (interval_continuousOn_mem a b _ (interval_weighted_polynomial_continuousOn a b ha n)).coeFn_toLp

lemma interval_weighted_polynomial_cancel (a b : ℝ) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    t * (intervalWeightedPolynomial a b n t)^2 = (intervalPolynomial a b n t)^2 := by
  unfold intervalWeightedPolynomial
  rw [div_pow, Real.sq_sqrt ht.le]
  exact mul_div_cancel₀ _ ht.ne'

lemma interval_weighted_trajectory_inner (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ⟪intervalWeightedTrajectory a b ha n,
      intervalMultiplication a b (intervalWeightedTrajectory a b ha n)⟫ =
      ‖intervalTrajectory a b n‖^2 := by
  rw [interval_multiplication_inner, interval_l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [interval_weighted_trajectory_coe a b ha n,
    interval_trajectory_coe a b n, ae_restrict_mem measurableSet_Icc] with t ht hg hmem
  rw [ht, hg]
  exact interval_weighted_polynomial_cancel a b n t (ha.trans_le hmem.1)

lemma interval_weighted_trajectory_image_norm_sq (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ‖intervalMultiplication a b (intervalWeightedTrajectory a b ha n)‖^2 =
      ⟪intervalTrajectory a b n, intervalMultiplication a b (intervalTrajectory a b n)⟫ := by
  rw [interval_l2_norm_sq_integral, interval_multiplication_inner]
  apply integral_congr_ae
  filter_upwards [interval_weighted_trajectory_coe a b ha n,
    interval_trajectory_coe a b n,
    interval_multiplication_coe a b (intervalWeightedTrajectory a b ha n),
    ae_restrict_mem measurableSet_Icc] with t ht hg hAt hmem
  change (intervalMultiplicationLinear a b (intervalWeightedTrajectory a b ha n) t)^2 = _
  rw [hAt, ht, hg, mul_pow]
  have h := interval_weighted_polynomial_cancel a b n t (ha.trans_le hmem.1)
  calc
    t^2 * (intervalWeightedPolynomial a b n t)^2 =
        t * (t * (intervalWeightedPolynomial a b n t)^2) := by ring
    _ = _ := congrArg (fun z : ℝ => t*z) h

lemma interval_weighted_trajectory_bb2 (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    operatorBB2 (intervalMultiplication a b).toLinearMap (intervalWeightedTrajectory a b ha n) =
      2/(a+b) := by
  unfold operatorBB2
  change ⟪intervalWeightedTrajectory a b ha n,
    intervalMultiplication a b (intervalWeightedTrajectory a b ha n)⟫ /
    ‖intervalMultiplication a b (intervalWeightedTrajectory a b ha n)‖^2 = _
  rw [interval_weighted_trajectory_inner, interval_weighted_trajectory_image_norm_sq]
  exact interval_trajectory_bb1 a b ha hab n

lemma interval_weighted_trajectory_step (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    intervalWeightedTrajectory a b ha (n+1) = operatorGradientStep
      (intervalMultiplication a b).toLinearMap (2/(a+b)) (intervalWeightedTrajectory a b ha n) := by
  apply Lp.ext
  have hsub := Lp.coeFn_sub (intervalWeightedTrajectory a b ha n)
    ((2/(a+b)) • intervalMultiplication a b (intervalWeightedTrajectory a b ha n))
  filter_upwards [interval_weighted_trajectory_coe a b ha (n+1),
    interval_weighted_trajectory_coe a b ha n,
    interval_multiplication_coe a b (intervalWeightedTrajectory a b ha n), hsub,
    Lp.coeFn_smul (2/(a+b)) (intervalMultiplication a b (intervalWeightedTrajectory a b ha n))]
      with t h1 h2 h3 h4 h5
  change intervalWeightedTrajectory a b ha (n+1) t =
    (intervalWeightedTrajectory a b ha n - (2/(a+b)) • intervalMultiplication a b
      (intervalWeightedTrajectory a b ha n)) t
  rw [h1, h4, Pi.sub_apply, h5, Pi.smul_apply, smul_eq_mul]
  change intervalWeightedPolynomial a b (n+1) t =
    intervalWeightedTrajectory a b ha n t - (2/(a+b)) *
      intervalMultiplicationLinear a b (intervalWeightedTrajectory a b ha n) t
  rw [h3, h2]
  simp only [intervalWeightedPolynomial, intervalPolynomial, pow_succ]
  ring

lemma interval_weighted_trajectory_matched_bb2 (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    intervalWeightedTrajectory a b ha 1 = operatorGradientStep
      (intervalMultiplication a b).toLinearMap
      (operatorBB2 (intervalMultiplication a b).toLinearMap (intervalWeightedTrajectory a b ha 0))
      (intervalWeightedTrajectory a b ha 0) ∧
    ∀ n, intervalWeightedTrajectory a b ha (n+2) = operatorGradientStep
      (intervalMultiplication a b).toLinearMap
      (operatorBB2 (intervalMultiplication a b).toLinearMap (intervalWeightedTrajectory a b ha n))
      (intervalWeightedTrajectory a b ha (n+1)) := by
  constructor
  · rw [interval_weighted_trajectory_bb2 a b ha hab]
    exact interval_weighted_trajectory_step a b ha 0
  · intro n
    rw [interval_weighted_trajectory_bb2 a b ha hab]
    exact interval_weighted_trajectory_step a b ha (n+1)

lemma interval_weighted_norm_upper (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ‖intervalWeightedTrajectory a b ha n‖ ≤ (Real.sqrt a)⁻¹ * ‖intervalTrajectory a b n‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [interval_weighted_trajectory_coe a b ha n,
    interval_trajectory_coe a b n, ae_restrict_mem measurableSet_Icc] with t ht hg hmem
  rw [ht, hg, intervalWeightedPolynomial, norm_div, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h := div_le_div_of_nonneg_left (abs_nonneg (intervalPolynomial a b n t))
    (Real.sqrt_pos.mpr ha) (Real.sqrt_le_sqrt hmem.1)
  simpa only [div_eq_mul_inv, mul_comm] using h

lemma interval_weighted_norm_lower (a b : ℝ) (ha : 0 < a) (n : ℕ) :
    ‖intervalTrajectory a b n‖ ≤ Real.sqrt b * ‖intervalWeightedTrajectory a b ha n‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [interval_weighted_trajectory_coe a b ha n,
    interval_trajectory_coe a b n, ae_restrict_mem measurableSet_Icc] with t ht hg hmem
  rw [ht, hg]
  have htp : 0 < Real.sqrt t := Real.sqrt_pos.mpr (ha.trans_le hmem.1)
  have he : intervalPolynomial a b n t = Real.sqrt t * intervalWeightedPolynomial a b n t := by
    unfold intervalWeightedPolynomial
    rw [mul_div_cancel₀ _ htp.ne']
  rw [he, norm_mul, Real.norm_eq_abs, abs_of_pos htp]
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hmem.2) (norm_nonneg _)

lemma interval_weighted_trajectory_norm_pos (a b : ℝ) (ha : 0 < a) (hab : a < b) (n : ℕ) :
    0 < ‖intervalWeightedTrajectory a b ha n‖ := by
  have hp := interval_trajectory_norm_pos a b ha hab n
  have hlo := interval_weighted_norm_lower a b ha n
  have hb : 0 < Real.sqrt b := Real.sqrt_pos.mpr (ha.trans hab)
  nlinarith

lemma interval_weighted_trajectory_rootFactor (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    rootFactor (fun n => ‖intervalWeightedTrajectory a b ha n‖ /
      ‖intervalWeightedTrajectory a b ha 0‖) = rate a b := by
  have hb := interval_trajectory_root_bounded a b ha hab
  have hsa : 0 < (Real.sqrt a)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr ha)
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr (ha.trans hab)
  have hbw := rootTerm_bounded_of_comparison
    (fun n => ‖intervalWeightedTrajectory a b ha n‖)
    (fun n => ‖intervalTrajectory a b n‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hb (Real.sqrt a)⁻¹ hsa
    (eventually_of_forall (interval_weighted_norm_upper a b ha))
  have heq := rootFactor_eq_of_comparable
    (fun n => ‖intervalWeightedTrajectory a b ha n‖)
    (fun n => ‖intervalTrajectory a b n‖) (fun _ => norm_nonneg _)
    (fun _ => norm_nonneg _) hb (Real.sqrt a)⁻¹ (Real.sqrt b) hsa hsb
    (eventually_of_forall (interval_weighted_norm_upper a b ha))
    (eventually_of_forall (interval_weighted_norm_lower a b ha))
  rw [rootFactor_div_const (fun n => ‖intervalWeightedTrajectory a b ha n‖)
    (fun _ => norm_nonneg _) hbw _ (interval_weighted_trajectory_norm_pos a b ha hab 0), heq]
  rw [← rootFactor_div_const (fun n => ‖intervalTrajectory a b n‖)
    (fun _ => norm_nonneg _) hb _ (interval_trajectory_norm_pos a b ha hab 0)]
  exact interval_trajectory_rootFactor a b ha hab

end
end BB
