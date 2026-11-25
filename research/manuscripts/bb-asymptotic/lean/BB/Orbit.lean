import BB.Spectral

/-!
# Exact finite-segment and periodic identities

These results apply to the real finite spectral update, including disappearing
interior coordinates. Endpoint positivity is explicit. Reduction of arbitrary
periodic supports to their extreme surviving coordinates is a separate obligation.
-/

namespace BB
noncomputable section
open scoped BigOperators

theorem sum_coboundary_identity (f D h : ℕ → ℝ) (β : ℝ)
    (hstep : ∀ k, f k = β - D k + h (k+1) - h k) (n : ℕ) :
    (∑ k in Finset.range n, f k) =
      (n : ℝ)*β - (∑ k in Finset.range n, D k) + h n - h 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, hstep n]
    push_cast
    ring

theorem sum_coboundary_le (f D h : ℕ → ℝ) (β : ℝ)
    (hstep : ∀ k, f k = β - D k + h (k+1) - h k)
    (hD : ∀ k, 0 ≤ D k) (n : ℕ) :
    (∑ k in Finset.range n, f k) ≤ (n : ℝ)*β + h n - h 0 := by
  rw [sum_coboundary_identity f D h β hstep n]
  have hh : 0 ≤ ∑ k in Finset.range n, D k :=
    Finset.sum_nonneg fun k _ => hD k
  linarith

theorem periodic_coboundary_average_le (f D h : ℕ → ℝ) (β : ℝ)
    (hstep : ∀ k, f k = β - D k + h (k+1) - h k)
    (hD : ∀ k, 0 ≤ D k) (n : ℕ) (hn : 0 < n) (hperiod : h n = h 0) :
    (∑ k in Finset.range n, f k) / (n : ℝ) ≤ β := by
  have hs := sum_coboundary_le f D h β hstep hD n
  rw [hperiod] at hs
  apply (div_le_iff (by exact_mod_cast hn : (0 : ℝ) < n)).mpr
  nlinarith only [hs]

theorem periodic_coboundary_average_eq_iff (f D h : ℕ → ℝ) (β : ℝ)
    (hstep : ∀ k, f k = β - D k + h (k+1) - h k)
    (hD : ∀ k, 0 ≤ D k) (n : ℕ) (hn : 0 < n) (hperiod : h n = h 0) :
    (∑ k in Finset.range n, f k) / (n : ℝ) = β ↔
      ∀ k < n, D k = 0 := by
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hn : (0 : ℝ) < n)
  have hid := sum_coboundary_identity f D h β hstep n
  rw [hperiod] at hid
  constructor
  · intro he
    have he' := (div_eq_iff hn0).mp he
    have hz : ∑ k in Finset.range n, D k = 0 := by nlinarith only [he', hid]
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hD k)).mp hz
    intro k hk
    exact hall k (Finset.mem_range.mpr hk)
  · intro hall
    have hz : ∑ k in Finset.range n, D k = 0 :=
      Finset.sum_eq_zero fun k hk => hall k (Finset.mem_range.mp hk)
    apply (div_eq_iff hn0).mpr
    nlinarith only [hid, hz]

variable {ι : Type*} [Fintype ι]

theorem spectral_orbit_log_identity {lam : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : ℕ → ι → ℝ)
    (hw : ∀ k, IsSimplex (w k)) (hz : ∀ k, IsSimplex (z k))
    (hwlo : ∀ k, 0 < w k lo) (hwhi : ∀ k, 0 < w k hi)
    (hzlo : ∀ k, 0 < z k lo) (hzhi : ∀ k, 0 < z k hi)
    (hupdate : ∀ k, w (k+1) = weightUpdate lam (w k) (z k)) (n : ℕ) :
    (∑ k in Finset.range n, Real.log (Real.sqrt (growthSq lam (w k) (z k)))) =
      (n : ℝ)*Real.log (rate a b) -
        (∑ k in Finset.range n, endpointDefect a b (mean lam (z k))) +
        endpointPotential a b (w n lo) (w n hi) - endpointPotential a b (w 0 lo) (w 0 hi) := by
  apply sum_coboundary_identity
  intro k
  rw [hupdate k]
  exact spectral_cohomology ha hab hlo hhi hlam (hw k) (hz k)
    (hwlo k) (hwhi k) (hzlo k) (hzhi k)

/-- Exact periodic average bound on a face with positive endpoint masses. -/
theorem spectral_periodic_average_le {lam : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : ℕ → ι → ℝ)
    (hw : ∀ k, IsSimplex (w k)) (hz : ∀ k, IsSimplex (z k))
    (hwlo : ∀ k, 0 < w k lo) (hwhi : ∀ k, 0 < w k hi)
    (hzlo : ∀ k, 0 < z k lo) (hzhi : ∀ k, 0 < z k hi)
    (hupdate : ∀ k, w (k+1) = weightUpdate lam (w k) (z k))
    (n : ℕ) (hn : 0 < n) (hperiod : w n = w 0) :
    (∑ k in Finset.range n, Real.log (Real.sqrt (growthSq lam (w k) (z k)))) /
      (n : ℝ) ≤ Real.log (rate a b) := by
  apply periodic_coboundary_average_le
    (fun k => Real.log (Real.sqrt (growthSq lam (w k) (z k))))
    (fun k => endpointDefect a b (mean lam (z k)))
    (fun k => endpointPotential a b (w k lo) (w k hi)) (Real.log (rate a b))
  · intro k
    rw [hupdate k]
    exact spectral_cohomology ha hab hlo hhi hlam (hw k) (hz k)
      (hwlo k) (hwhi k) (hzlo k) (hzhi k)
  · intro k
    obtain ⟨h1,h2,_⟩ := endpoint_state_regular ha hab hlo hhi hlam (hw k) (hz k)
      (hwlo k) (hzlo k) (hzhi k)
    exact endpoint_defect_nonneg ha h1 h2
  · exact hn
  · rw [hperiod]

/-- Equality forces the delayed spectral mean to be the midpoint at every step. -/
theorem spectral_periodic_average_eq_iff {lam : ι → ℝ} {lo hi : ι} {a b : ℝ}
    (ha : 0 < a) (hab : a < b)
    (hlo : lam lo = a) (hhi : lam hi = b)
    (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (w z : ℕ → ι → ℝ)
    (hw : ∀ k, IsSimplex (w k)) (hz : ∀ k, IsSimplex (z k))
    (hwlo : ∀ k, 0 < w k lo) (hwhi : ∀ k, 0 < w k hi)
    (hzlo : ∀ k, 0 < z k lo) (hzhi : ∀ k, 0 < z k hi)
    (hupdate : ∀ k, w (k+1) = weightUpdate lam (w k) (z k))
    (n : ℕ) (hn : 0 < n) (hperiod : w n = w 0) :
    (∑ k in Finset.range n, Real.log (Real.sqrt (growthSq lam (w k) (z k)))) /
      (n : ℝ) = Real.log (rate a b) ↔
      ∀ k < n, mean lam (z k) = (a+b)/2 := by
  have hstep : ∀ k, Real.log (Real.sqrt (growthSq lam (w k) (z k))) =
      Real.log (rate a b) - endpointDefect a b (mean lam (z k)) +
        endpointPotential a b (w (k+1) lo) (w (k+1) hi) -
        endpointPotential a b (w k lo) (w k hi) := by
    intro k
    rw [hupdate k]
    exact spectral_cohomology ha hab hlo hhi hlam (hw k) (hz k)
      (hwlo k) (hwhi k) (hzlo k) (hzhi k)
  have hinside : ∀ k, a < mean lam (z k) ∧ mean lam (z k) < b := by
    intro k
    obtain ⟨h1,h2,_⟩ := endpoint_state_regular ha hab hlo hhi hlam (hw k) (hz k)
      (hwlo k) (hzlo k) (hzhi k)
    exact ⟨h1,h2⟩
  have hnonneg : ∀ k, 0 ≤ endpointDefect a b (mean lam (z k)) :=
    fun k => endpoint_defect_nonneg ha (hinside k).1 (hinside k).2
  have hreturn : endpointPotential a b (w n lo) (w n hi) =
      endpointPotential a b (w 0 lo) (w 0 hi) := by rw [hperiod]
  rw [periodic_coboundary_average_eq_iff
    (fun k => Real.log (Real.sqrt (growthSq lam (w k) (z k))))
    (fun k => endpointDefect a b (mean lam (z k)))
    (fun k => endpointPotential a b (w k lo) (w k hi))
    (Real.log (rate a b)) hstep hnonneg n hn hreturn]
  apply forall_congr'
  intro k
  apply forall_congr'
  intro _
  exact endpoint_defect_eq_zero_iff ha (hinside k).1 (hinside k).2

end
end BB
