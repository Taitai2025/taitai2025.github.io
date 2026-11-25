import BB.Dini
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Every positive Hölder exponent gives a Dini modulus -/

noncomputable section
namespace BB.Dini
open Set Filter MeasureTheory
open scoped Topology

/-- A total monotone version of the usual Hölder modulus on nonnegative radii. -/
def holderModulus (C theta t : ℝ) : ℝ := C*(max t 0)^theta

theorem holderModulus_nonnegative {C theta t : ℝ} (hC : 0 ≤ C) :
    0 ≤ holderModulus C theta t :=
  mul_nonneg hC (Real.rpow_nonneg (le_max_right _ _) _)

theorem holderModulus_monotone {C theta : ℝ} (hC : 0 ≤ C) (htheta : 0 ≤ theta) :
    Monotone (holderModulus C theta) := by
  intro s t hst
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (le_max_right _ _) (max_le_max hst le_rfl) htheta) hC

theorem holderModulus_eq {C theta t : ℝ} (ht : 0 ≤ t) :
    holderModulus C theta t=C*t^theta := by simp only [holderModulus,max_eq_left ht]

theorem holderModulus_tendsto_zero (C : ℝ) {theta : ℝ} (htheta : 0 < theta) :
    Tendsto (holderModulus C theta) (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 0) := by
  have hc : Continuous (holderModulus C theta) :=
    continuous_const.mul ((continuous_id.max continuous_const).rpow_const (fun _ => Or.inr htheta.le))
  have hzero : holderModulus C theta 0=0 := by simp [holderModulus,Real.zero_rpow htheta.ne']
  have hh := (hc.tendsto 0).mono_left
    (nhdsWithin_le_nhds : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓝 0)
  simpa only [hzero] using hh

private theorem holder_integrand_eq {C theta t : ℝ} (ht : 0 < t) :
    holderModulus C theta t/t=C*t^(theta-1) := by
  rw [holderModulus_eq ht.le,Real.rpow_sub_one ht.ne' theta]
  ring

theorem holderModulus_dini (C : ℝ) {theta R : ℝ} (htheta : 0 < theta) (hR : 0 ≤ R) :
    IntervalIntegrable (fun t => holderModulus C theta t/t) volume 0 R := by
  have hp : IntervalIntegrable (fun t : ℝ => C*t^(theta-1)) volume 0 R :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith only [htheta] : -1 < theta-1)).const_mul C
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR] at hp ⊢
  exact hp.congr_fun (fun t ht => (holder_integrand_eq ht.1).symm) measurableSet_Ioc

/-- The Dini integral has the standard explicit Hölder bound. -/
theorem holderModulus_dini_integral (C : ℝ) {theta R : ℝ}
    (htheta : 0 < theta) (hR : 0 ≤ R) :
    (∫ t in (0 : ℝ)..R,holderModulus C theta t/t)=C*R^theta/theta := by
  calc
    (∫ t in (0 : ℝ)..R,holderModulus C theta t/t) =
        ∫ t in (0 : ℝ)..R,C*t^(theta-1) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t
      intro ht
      rw [uIoc_of_le hR] at ht
      exact holder_integrand_eq ht.1
    _ = C*((R^((theta-1)+1)-(0 : ℝ)^((theta-1)+1))/((theta-1)+1)) := by
      rw [intervalIntegral.integral_const_mul,integral_rpow (Or.inl (by linarith only [htheta] : -1 < theta-1))]
    _ = C*R^theta/theta := by
      rw [sub_add_cancel,Real.zero_rpow htheta.ne',sub_zero]
      ring

end BB.Dini
