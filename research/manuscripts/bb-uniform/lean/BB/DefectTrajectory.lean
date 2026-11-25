import BB.DefectMidpoint
import BB.DefectLimits

/-! # Cumulative and asymptotic defect results for actual endpoint components

Every energy identity in this module is derived from the two endpoint update
formulas.  No dissipation law is assumed independently of the trajectory.
-/

noncomputable section
namespace BB.Defect
open Filter
open scoped Topology BigOperators

/-- A nonterminal spectral tail with both extreme components surviving. -/
structure EndpointTrajectory (a b : ℝ) where
  tau : ℕ → ℝ
  lowSize : ℕ → ℝ
  highSize : ℕ → ℝ
  tau_lower : ∀ n, a < tau n
  tau_upper : ∀ n, tau n < b
  low_initial : 0 < lowSize 0
  high_initial : 0 < highSize 0
  low_step : ∀ n, lowSize (n+1)=((tau n-a)/(tau n))*lowSize n
  high_step : ∀ n, highSize (n+1)=((b-tau n)/(tau n))*highSize n

namespace EndpointTrajectory
variable {a b : ℝ} (T : EndpointTrajectory a b)

def energy (n : ℕ) : ℝ := BB.geometricProduct (BB.endpointTheta a b) (T.lowSize n) (T.highSize n)^2

def defect (n : ℕ) : ℝ := BB.endpointDefect a b (T.tau n)

theorem sizes_positive (ha : 0 < a) (n : ℕ) : 0 < T.lowSize n ∧ 0 < T.highSize n := by
  induction n with
  | zero => exact ⟨T.low_initial,T.high_initial⟩
  | succ n ih =>
    have ht : 0 < T.tau n := ha.trans (T.tau_lower n)
    rw [T.low_step,T.high_step]
    exact ⟨mul_pos (div_pos (sub_pos.mpr (T.tau_lower n)) ht) ih.1,
      mul_pos (div_pos (sub_pos.mpr (T.tau_upper n)) ht) ih.2⟩

theorem energy_positive (ha : 0 < a) (n : ℕ) : 0 < T.energy n :=
  sq_pos_of_pos (BB.geometricProduct_pos (T.sizes_positive ha n).1 (T.sizes_positive ha n).2)

theorem defect_nonnegative (ha : 0 < a) (n : ℕ) : 0 ≤ T.defect n :=
  BB.endpointDefect_nonneg ha (T.tau_lower n) (T.tau_upper n)

theorem exact_step (ha : 0 < a) (n : ℕ) :
    T.energy (n+1)=BB.endpointRate a b^2*Real.exp (-2*T.defect n)*T.energy n := by
  unfold energy defect
  rw [T.low_step,T.high_step]
  exact BB.endpointEnergy_exact ha (T.tau_lower n) (T.tau_upper n)
    (T.sizes_positive ha n).1.le (T.sizes_positive ha n).2.le

/-- Baseline Corollary 3.2's exact cumulative dissipation formula. -/
theorem cumulative (ha : 0 < a) (n : ℕ) :
    T.energy n=BB.endpointRate a b^(2*n)*
      Real.exp (-2*∑ j in Finset.range n,T.defect j)*T.energy 0 :=
  BB.cumulative_dissipation T.energy T.defect (BB.endpointRate a b) (T.exact_step ha) n

/-- The normalized actual endpoint energy is nonincreasing. -/
theorem normalized_antitone (ha : 0 < a) :
    Antitone (fun n => T.energy n/BB.endpointRate a b^(2*n)) :=
  normalized_energy_antitone (BB.endpointRate_pos ha ((T.tau_lower 0).trans (T.tau_upper 0)))
    (T.energy_positive ha 0).le (T.defect_nonnegative ha) (T.exact_step ha)

/-- Every positive limiting lower mean improves the actual energy root factor. -/
theorem strict_factor (ha : 0 < a) (hmean : 0 < liminf (average T.defect) atTop) :
    limsup (rootEnergy T.energy) atTop < BB.endpointRate a b^2 :=
  limsup_lt_of_positive_liminf (BB.endpointRate_pos ha ((T.tau_lower 0).trans (T.tau_upper 0)))
    (T.energy_positive ha 0) (T.defect_nonnegative ha) (T.exact_step ha) hmean

/-- Full asymptotic extremality is exactly vanishing average defect. -/
theorem root_limit_iff_average_zero (ha : 0 < a) :
    Tendsto (rootEnergy T.energy) atTop (𝓝 (BB.endpointRate a b^2)) ↔
      Tendsto (average T.defect) atTop (𝓝 0) := by
  have hc := BB.endpointRate_pos ha ((T.tau_lower 0).trans (T.tau_upper 0))
  constructor
  · exact average_zero_of_extremal_root_limit hc (T.energy_positive ha 0) (T.exact_step ha)
  · intro hmean
    simpa using root_limit_of_average_limit hc (T.energy_positive ha 0) (T.exact_step ha) hmean

/-- A critical limsup yields only zero liminf of the mean defect. -/
theorem limsup_extremality (ha : 0 < a)
    (hroot : limsup (rootEnergy T.energy) atTop=BB.endpointRate a b^2) :
    liminf (average T.defect) atTop=0 :=
  liminf_average_zero_of_extremal_limsup
    (BB.endpointRate_pos ha ((T.tau_lower 0).trans (T.tau_upper 0)))
    (T.energy_positive ha 0) (T.defect_nonnegative ha) (T.exact_step ha) hroot

/-- The precise meaning of reciprocal steps spending almost all their time near
the midpoint: every fixed outside-neighborhood frequency tends to zero. -/
theorem midpoint_concentration (ha : 0 < a)
    (hroot : Tendsto (rootEnergy T.energy) atTop (𝓝 (BB.endpointRate a b^2)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fraction (fun n => epsilon ≤ |T.tau n-(a+b)/2|)) atTop (𝓝 0) :=
  midpoint_density_of_extremal_root_limit ha ((T.tau_lower 0).trans (T.tau_upper 0))
    T.tau T.energy T.tau_lower T.tau_upper (T.energy_positive ha 0) (T.exact_step ha) hroot hepsilon

end EndpointTrajectory
end BB.Defect
