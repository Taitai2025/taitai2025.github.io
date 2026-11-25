import BB.Spectral
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The fixed exponential-weight comparison in the introduction

The comparison is proved directly by a symmetrized finite covariance identity.
No external convergence theorem is used as an axiom.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Comparison

open BB.Spectral
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Exact finite covariance identity, with no positivity assumptions. -/
theorem covariance_identity (lam w psi e : ι → ℝ) :
    (∑ i, ∑ j, e i*e j*(psi i*w j-psi j*w i)*(lam j-lam i)) =
      2*(numerator psi e*denominator lam w e-denominator lam psi e*numerator w e) := by
  let F : ι → ι → ℝ := fun i j => e i*e j*psi i*w j*(lam j-lam i)
  have hA : numerator psi e*denominator lam w e =
      ∑ i, ∑ j, e i*e j*psi i*w j*lam j := by
    unfold numerator denominator
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hB : denominator lam psi e*numerator w e =
      ∑ i, ∑ j, e i*e j*psi i*w j*lam i := by
    unfold numerator denominator
    rw [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hF : (∑ i, ∑ j, F i j) =
      numerator psi e*denominator lam w e-denominator lam psi e*numerator w e := by
    rw [hA,hB]
    simp_rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [F]
    ring
  calc
    (∑ i, ∑ j, e i*e j*(psi i*w j-psi j*w i)*(lam j-lam i)) =
        ∑ i, ∑ j, (F i j+F j i) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp [F]
      ring
    _ = (∑ i, ∑ j, F i j)+(∑ i, ∑ j, F j i) := by simp_rw [Finset.sum_add_distrib]
    _ = 2*(∑ i, ∑ j, F i j) := by rw [Finset.sum_comm (f := fun i j => F j i)]; ring
    _ = _ := by rw [hF]

/-- Ordering the relative weights reverses the weighted Rayleigh mean and
therefore orders the reciprocal stepsizes in the required direction. -/
theorem quotient_comparison [LinearOrder ι] {lam w psi e : ι → ℝ}
    (hmono : Monotone lam) (he : ∀ i, 0 ≤ e i)
    (horder : ∀ i j, i < j → psi j*w i ≤ psi i*w j)
    (hdw : 0 < denominator lam w e) (hdp : 0 < denominator lam psi e) :
    alpha lam w e ≤ alpha lam psi e := by
  have hs : 0 ≤ ∑ i, ∑ j, e i*e j*(psi i*w j-psi j*w i)*(lam j-lam i) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    have hprod : 0 ≤ (psi i*w j-psi j*w i)*(lam j-lam i) := by
      rcases lt_trichotomy i j with hij | hij | hij
      · exact mul_nonneg (sub_nonneg.mpr (horder i j hij)) (sub_nonneg.mpr (hmono hij.le))
      · simp [hij]
      · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (horder j i hij))
          (sub_nonpos.mpr (hmono hij.le))
    nlinarith only [mul_nonneg (mul_nonneg (he i) (he j)) hprod]
  rw [covariance_identity] at hs
  apply (div_le_div_iff hdw hdp).mpr
  nlinarith only [hs]

/-- A uniform adjacent spectral gap is a lower bound for every positive gap. -/
theorem adjacent_gap_bound {n : ℕ} {lam : Fin (n+2) → ℝ} {Delta : ℝ}
    (hmono : Monotone lam)
    (hgap : ∀ i : Fin (n+1), Delta ≤ lam i.succ-lam i.castSucc) :
    ∀ i j : Fin (n+2), i < j → Delta ≤ lam j-lam i := by
  intro i j hij
  let k : Fin (n+1) := ⟨i.val,by have := j.isLt; have : i.val < j.val := hij; omega⟩
  have hk : k.castSucc = i := by apply Fin.ext; rfl
  have hkj : k.succ ≤ j := by change i.val+1 ≤ j.val; have : i.val < j.val := hij; omega
  have hh := hgap k
  rw [hk] at hh
  linarith only [hh,hmono hkj]

/-- One fixed positive exponential weight dominates every weight vector with
the prescribed condition bound, exactly as asserted in the introduction. -/
theorem exponential_weight_comparison {n : ℕ} (lam : Fin (n+2) → ℝ)
    (hmono : StrictMono lam) (ha : 0 < lam 0)
    {chi Delta t : ℝ} (hchi : 1 ≤ chi) (hDelta : 0 < Delta)
    (hgap : ∀ i : Fin (n+1), Delta ≤ lam i.succ-lam i.castSucc)
    (ht : t*Delta ≥ Real.log chi)
    (w e : Fin (n+2) → ℝ) (hw1 : ∀ i, 1 ≤ w i) (hwchi : ∀ i, w i ≤ chi)
    (he : ∀ i, 0 ≤ e i) (hE : 0 < mass e) :
    alpha lam w e ≤ alpha lam (fun i => Real.exp (-t*lam i)) e := by
  have hchip : 0 < chi := lt_of_lt_of_le zero_lt_one hchi
  have ht0 : 0 ≤ t := by
    have hlog : 0 ≤ Real.log chi := Real.log_nonneg hchi
    nlinarith only [ht,hlog,hDelta]
  let b := lam (Fin.last (n+1))
  let psi : Fin (n+2) → ℝ := fun i => Real.exp (-t*lam i)
  have hpsi : ∀ i, Real.exp (-t*b) ≤ psi i := by
    intro i
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (hmono.monotone (Fin.le_last i)) ht0
    dsimp [b] at *
    linarith only [hh]
  have hnumw : 0 < numerator w e := numerator_pos he (by norm_num) hw1 hE
  have hnump : 0 < numerator psi e := numerator_pos he (Real.exp_pos _) hpsi hE
  have hloa := fun i => hmono.monotone (Fin.zero_le i)
  have hhib := fun i => hmono.monotone (Fin.le_last i)
  have hdw : 0 < denominator lam w e := (mul_pos ha hnumw).trans_le
    (denominator_bounds he (fun i => (by norm_num : (0:ℝ) ≤ 1).trans (hw1 i)) hloa hhib).1
  have hdp : 0 < denominator lam psi e := (mul_pos ha hnump).trans_le
    (denominator_bounds he (fun i => (Real.exp_pos _).le) hloa hhib).1
  apply quotient_comparison hmono.monotone he ?_ hdw hdp
  intro i j hij
  have hdiff := adjacent_gap_bound hmono.monotone hgap i j hij
  have hlog : Real.log chi ≤ t*(lam j-lam i) :=
    ht.trans (mul_le_mul_of_nonneg_left hdiff ht0)
  have hexp : chi ≤ Real.exp (t*(lam j-lam i)) := by
    rw [← Real.exp_log hchip]
    exact Real.exp_le_exp.mpr hlog
  have hident : psi i = Real.exp (t*(lam j-lam i))*psi j := by
    dsimp [psi]
    rw [← Real.exp_add]
    congr 1
    ring
  have hpj : 0 ≤ psi j := (Real.exp_pos _).le
  have hwj : 0 ≤ w j := (by norm_num : (0:ℝ) ≤ 1).trans (hw1 j)
  have hp := mul_le_mul_of_nonneg_right hexp hpj
  rw [← hident] at hp
  have h1 := mul_le_mul_of_nonneg_right hp hwj
  have h2 := mul_le_mul_of_nonneg_left (hw1 j) hchip.le
  have hwi : w i ≤ chi*w j := (hwchi i).trans (by nlinarith only [h2])
  have h3 := mul_le_mul_of_nonneg_left hwi hpj
  nlinarith only [h1,h3]

end BB.Comparison
