import BB.Endpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! # Consequences of the exact cumulative defect identity

The strict-rate hypothesis is written as an eventual positive lower bound for
the average defect, which also includes an infinite extended liminf.  Full
root-limit extremality implies a vanishing average.  Limsup extremality alone
only yields arbitrarily late small averages, stated using `Frequently`.
-/

noncomputable section
namespace BB.Defect
open Set Filter
open scoped Topology BigOperators

/-- Cesàro average of the defect; the value at index zero is the harmless total extension. -/
def average (D : ℕ → ℝ) (n : ℕ) : ℝ := (∑ j in Finset.range n,D j)/(n : ℝ)

def rootEnergy (E : ℕ → ℝ) (n : ℕ) : ℝ := E n^(1/(n : ℝ))

variable {E D : ℕ → ℝ} {c : ℝ}

theorem average_nonnegative (hD : ∀ n, 0 ≤ D n) (n : ℕ) : 0 ≤ average D n :=
  div_nonneg (Finset.sum_nonneg (fun j _ => hD j)) (Nat.cast_nonneg _)

theorem energy_positive (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n) (n : ℕ) : 0 < E n := by
  rw [BB.cumulative_dissipation E D c hstep n]
  exact mul_pos (mul_pos (pow_pos hc _) (Real.exp_pos _)) hE

/-- The worst-rate-normalized energy is nonincreasing. -/
theorem normalized_energy_antitone (hc : 0 < c) (hE : 0 ≤ E 0)
    (hD : ∀ n, 0 ≤ D n)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n) :
    Antitone (fun n => E n/c^(2*n)) := by
  have hid (n : ℕ) : E n/c^(2*n)=Real.exp (-2*∑ j in Finset.range n,D j)*E 0 := by
    rw [BB.cumulative_dissipation E D c hstep n]
    field_simp [(pow_pos hc (2*n)).ne']
    ring
  apply antitone_nat_of_succ_le
  intro n
  rw [hid,hid,Finset.sum_range_succ]
  apply mul_le_mul_of_nonneg_right _ hE
  apply Real.exp_le_exp.mpr
  nlinarith only [hD n]

theorem log_energy (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n) (n : ℕ) :
    Real.log (E n)=2*(n : ℝ)*Real.log c-2*(∑ j in Finset.range n,D j)+Real.log (E 0) := by
  rw [BB.cumulative_dissipation E D c hstep n,
    Real.log_mul (mul_pos (pow_pos hc _) (Real.exp_pos _)).ne' hE.ne',
    Real.log_mul (pow_pos hc _).ne' (Real.exp_pos _).ne',Real.log_pow,Real.log_exp]
  push_cast
  ring

theorem log_root_energy (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n) {n : ℕ} (hn : n ≠ 0) :
    Real.log (rootEnergy E n)=2*Real.log c-2*average D n+Real.log (E 0)/(n : ℝ) := by
  rw [rootEnergy,Real.log_rpow (energy_positive hc hE hstep n),log_energy hc hE hstep n]
  unfold average
  field_simp [Nat.cast_ne_zero.mpr hn]
  ring

/-- A convergent average gives the exact energy root factor. -/
theorem root_limit_of_average_limit (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n) {d : ℝ}
    (havg : Tendsto (average D) atTop (𝓝 d)) :
    Tendsto (rootEnergy E) atTop (𝓝 (c^2*Real.exp (-2*d))) := by
  have hconst : Tendsto (fun n : ℕ => Real.log (E 0)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun n => Real.log (rootEnergy E n)) atTop (𝓝 (2*Real.log c-2*d)) := by
    have hlim := ((tendsto_const_nhds (x := 2*Real.log c)).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul havg)).add hconst
    simp only [add_zero] at hlim
    apply hlim.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact (log_root_energy hc hE hstep (by omega : n ≠ 0)).symm
  have hexp := hlog.rexp
  have hid : Real.exp (2*Real.log c-2*d)=c^2*Real.exp (-2*d) := by
    rw [sub_eq_add_neg,Real.exp_add]
    rw [show 2*Real.log c=Real.log c+Real.log c by ring,Real.exp_add,Real.exp_log hc]
    ring
  rw [hid] at hexp
  convert hexp using 1
  ext n
  exact (Real.exp_log (Real.rpow_pos_of_pos (energy_positive hc hE hstep n) _)).symm

/-- Full root-limit extremality forces the average defect to tend to zero. -/
theorem average_zero_of_extremal_root_limit (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n)
    (hroot : Tendsto (rootEnergy E) atTop (𝓝 (c^2))) :
    Tendsto (average D) atTop (𝓝 0) := by
  have hlog := (Real.continuousAt_log (sq_pos_of_pos hc).ne').tendsto.comp hroot
  have hconst : Tendsto (fun n : ℕ => Real.log (E 0)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hlim := (((tendsto_const_nhds (x := 2*Real.log c)).add hconst).sub hlog).div_const 2
  have hlim' : Tendsto (fun n : ℕ =>
      (2*Real.log c+Real.log (E 0)/(n : ℝ)-Real.log (rootEnergy E n))/2) atTop (𝓝 0) := by
    convert hlim using 1
    rw [Real.log_pow]
    norm_num
  apply hlim'.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hid := log_root_energy hc hE hstep (by omega : n ≠ 0)
  linarith only [hid]

/-- The positive-liminf condition, in its equivalent eventual lower-bound form,
gives a strict asymptotic factor smaller than the worst endpoint factor. -/
theorem strict_factor_of_positive_average (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n)
    {d : ℝ} (hd : 0 < d) (havg : ∀ᶠ n in atTop, d ≤ average D n) :
    ∃ q : ℝ, 0 < q ∧ q < c^2 ∧ ∀ᶠ n in atTop, rootEnergy E n ≤ q := by
  let q := c^2*Real.exp (-d)
  have hq : 0 < q := mul_pos (sq_pos_of_pos hc) (Real.exp_pos _)
  have hqsmall : q < c^2 := by
    have he : Real.exp (-d) < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd)
    simpa only [mul_one] using mul_lt_mul_of_pos_left he (sq_pos_of_pos hc)
  have hconst : Tendsto (fun n : ℕ => Real.log (E 0)/(n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine ⟨q,hq,hqsmall,?_⟩
  filter_upwards [havg,hconst.eventually (gt_mem_nhds hd),eventually_ge_atTop (1 : ℕ)] with n hn hc0 hn1
  have hlog := log_root_energy hc hE hstep (by omega : n ≠ 0)
  have hlogbound : Real.log (rootEnergy E n) ≤ 2*Real.log c-d := by
    linarith only [hlog,hn,hc0]
  calc
    rootEnergy E n = Real.exp (Real.log (rootEnergy E n)) :=
      (Real.exp_log (Real.rpow_pos_of_pos (energy_positive hc hE hstep n) _)).symm
    _ ≤ Real.exp (2*Real.log c-d) := Real.exp_le_exp.mpr hlogbound
    _ = q := by
      rw [sub_eq_add_neg,Real.exp_add,
        show 2*Real.log c=Real.log c+Real.log c by ring,Real.exp_add,Real.exp_log hc]
      dsimp [q]
      ring

/-- Limsup extremality has the weaker consequence that arbitrarily late average
defects are small. It does not assert convergence of the average. -/
theorem average_frequently_small_of_extremal_limsup (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n)
    (hextreme : ∀ q : ℝ, q < c^2 → ∃ᶠ n in atTop, q < rootEnergy E n)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ᶠ n in atTop, average D n < epsilon := by
  change ¬ (∀ᶠ n in atTop, ¬ average D n < epsilon)
  intro hnot
  have havg : ∀ᶠ n in atTop, epsilon ≤ average D n := hnot.mono (fun _ h => le_of_not_gt h)
  obtain ⟨q,_,hq,hbound⟩ := strict_factor_of_positive_average hc hE hstep hepsilon havg
  obtain ⟨n,hn⟩ := ((hextreme q hq).and_eventually hbound).exists
  exact hn.2.not_lt hn.1

end BB.Defect
