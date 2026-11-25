import BB.DefectAsymptotics

/-! # Liminf and limsup formulations of endpoint dissipation -/

noncomputable section
namespace BB.Defect
open Filter
open scoped Topology

variable {E D : ℕ → ℝ} {c : ℝ}

theorem root_bounded_below (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n) :
    IsBoundedUnder (· ≥ ·) atTop (rootEnergy E) :=
  isBoundedUnder_of ⟨0,fun n => (Real.rpow_pos_of_pos (energy_positive hc hE hstep n) _).le⟩

/-- A positive eventual lower mean gives a strictly smaller energy root limsup. -/
theorem limsup_lt_of_positive_average (hc : 0 < c) (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n)
    {d : ℝ} (hd : 0 < d) (havg : ∀ᶠ n in atTop, d ≤ average D n) :
    limsup (rootEnergy E) atTop < c^2 := by
  obtain ⟨q,_,hq,hbound⟩ := strict_factor_of_positive_average hc hE hstep hd havg
  exact (Filter.limsup_le_of_le (root_bounded_below hc hE hstep).isCoboundedUnder_le hbound).trans_lt hq

/-- The baseline's positive-liminf hypothesis, with the real-valued liminf. The
preceding eventual formulation also covers average defects tending to infinity. -/
theorem limsup_lt_of_positive_liminf (hc : 0 < c) (hE : 0 < E 0)
    (hD : ∀ n, 0 ≤ D n)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n)
    (hliminf : 0 < liminf (average D) atTop) :
    limsup (rootEnergy E) atTop < c^2 := by
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (average D) :=
    isBoundedUnder_of ⟨0,average_nonnegative hD⟩
  have hlarge := Filter.eventually_lt_of_lt_liminf (half_lt_self hliminf) hbdd
  exact limsup_lt_of_positive_average hc hE hstep (half_pos hliminf)
    (hlarge.mono (fun _ h => h.le))

/-- If only the root limsup is critical, the justified conclusion is a zero
liminf of the average defect. Full mean convergence requires a full root limit. -/
theorem liminf_average_zero_of_extremal_limsup (hc : 0 < c) (hE : 0 < E 0)
    (hD : ∀ n, 0 ≤ D n)
    (hstep : ∀ n, E (n+1)=c^2*Real.exp (-2*D n)*E n)
    (hlimsup : limsup (rootEnergy E) atTop=c^2) :
    liminf (average D) atTop=0 := by
  have hextreme : ∀ q : ℝ, q < c^2 → ∃ᶠ n in atTop, q < rootEnergy E n := by
    intro q hq
    apply Filter.frequently_lt_of_lt_limsup (root_bounded_below hc hE hstep).isCoboundedUnder_le
    simpa only [hlimsup] using hq
  have hsmall : ∀ epsilon : ℝ, 0 < epsilon → ∃ᶠ n in atTop, average D n < epsilon :=
    fun _ hepsilon => average_frequently_small_of_extremal_limsup hc hE hstep hextreme hepsilon
  have hbdd : IsBoundedUnder (· ≥ ·) atTop (average D) :=
    isBoundedUnder_of ⟨0,average_nonnegative hD⟩
  have hcobdd : IsCoboundedUnder (· ≥ ·) atTop (average D) := by
    refine ⟨1,?_⟩
    intro A hA
    change ∀ᶠ n in atTop, A ≤ average D n at hA
    obtain ⟨n,hn⟩ := ((hsmall 1 zero_lt_one).and_eventually hA).exists
    exact hn.2.trans hn.1.le
  have hlo : 0 ≤ liminf (average D) atTop :=
    Filter.le_liminf_of_le hcobdd (eventually_of_forall (average_nonnegative hD))
  have hhi : liminf (average D) atTop ≤ 0 := by
    by_contra hnot
    have hp : 0 < liminf (average D) atTop := lt_of_not_ge hnot
    have hf := hsmall _ (half_pos hp)
    have hh := Filter.liminf_le_of_frequently_le (hf.mono (fun _ h => h.le)) hbdd
    exact (half_lt_self hp).not_le hh
  exact le_antisymm hhi hlo

end BB.Defect
