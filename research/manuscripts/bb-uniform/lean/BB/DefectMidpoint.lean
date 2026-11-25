import BB.DefectAsymptotics

/-! # Vanishing mean defect forces concentration near the reciprocal midpoint -/

noncomputable section
namespace BB.Defect
open Set Filter
open scoped Topology BigOperators

/-- The endpoint multiplier is continuous on the closed spectral interval,
including the two terminal endpoint values. -/
theorem endpointMultiplier_continuousOn {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContinuousOn (BB.endpointMultiplier a b) (Icc a b) := by
  have hden : ∀ t ∈ Icc a b, t ≠ 0 := fun t ht => (ha.trans_le ht.1).ne'
  have hx : ContinuousOn (fun t : ℝ => (t-a)/t) (Icc a b) :=
    (continuousOn_id.sub continuousOn_const).div continuousOn_id hden
  have hy : ContinuousOn (fun t : ℝ => (b-t)/t) (Icc a b) :=
    (continuousOn_const.sub continuousOn_id).div continuousOn_id hden
  exact (hx.rpow_const (fun _ _ => Or.inr (BB.endpointTheta_pos ha hab).le)).mul
    (hy.rpow_const (fun _ _ => Or.inr (sub_nonneg.mpr (BB.endpointTheta_lt_one ha hab).le)))

/-- Every fixed separation from the unique midpoint maximizer has a strictly
positive defect gap, uniformly over all interior reciprocal steps. -/
theorem endpointDefect_gap {a b epsilon : ℝ} (ha : 0 < a) (hab : a < b)
    (hepsilon : 0 < epsilon) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ t : ℝ, a < t → t < b →
      epsilon ≤ |t-(a+b)/2| → delta ≤ BB.endpointDefect a b t := by
  let K := Icc a b ∩ {t : ℝ | epsilon ≤ |t-(a+b)/2|}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const)))
  by_cases hne : K.Nonempty
  · obtain ⟨t,ht,hmax⟩ := hK.exists_isMaxOn hne
      ((endpointMultiplier_continuousOn ha hab).mono (inter_subset_left _ _))
    have hc : 0 < BB.endpointRate a b := BB.endpointRate_pos ha hab
    have hnotmid : t ≠ (a+b)/2 := by
      intro heq
      have hh : epsilon ≤ |t-(a+b)/2| := ht.2
      rw [heq,sub_self,abs_zero] at hh
      exact hepsilon.not_le hh
    have hstrict : BB.endpointMultiplier a b t < BB.endpointRate a b :=
      lt_of_le_of_ne (BB.endpointMultiplier_le ha hab ht.1.1 ht.1.2)
        (fun heq => hnotmid ((BB.endpointMultiplier_eq_iff ha hab ht.1.1 ht.1.2).mp heq))
    let m := max (BB.endpointMultiplier a b t) (BB.endpointRate a b/2)
    have hm : 0 < m := (half_pos hc).trans_le (le_max_right _ _)
    have hmc : m < BB.endpointRate a b := max_lt hstrict (half_lt_self hc)
    let delta := Real.log (BB.endpointRate a b)-Real.log m
    have hd : 0 < delta := sub_pos.mpr (Real.log_lt_log hm hmc)
    refine ⟨delta,hd,?_⟩
    intro u hua hub hu
    have huK : u ∈ K := ⟨⟨hua.le,hub.le⟩,hu⟩
    have hmaxu : BB.endpointMultiplier a b u ≤ BB.endpointMultiplier a b t := hmax huK
    have hule : BB.endpointMultiplier a b u ≤ m := hmaxu.trans (le_max_left _ _)
    have hu0 : 0 < u := ha.trans hua
    have hmul : 0 < BB.endpointMultiplier a b u :=
      BB.geometricProduct_pos (div_pos (sub_pos.mpr hua) hu0) (div_pos (sub_pos.mpr hub) hu0)
    rw [BB.endpointDefect_eq_log_ratio ha hua hub]
    exact sub_le_sub_left (Real.log_le_log hmul hule) _
  · refine ⟨1,zero_lt_one,?_⟩
    intro t hta htb ht
    exact (hne ⟨t,⟨⟨hta.le,htb.le⟩,ht⟩⟩).elim

/-- The fraction of indices among the first n satisfying a decidable event. -/
def fraction (p : ℕ → Prop) [DecidablePred p] (n : ℕ) : ℝ :=
  (((Finset.range n).filter p).card : ℝ)/(n : ℝ)

/-- A discrete Markov inequality transfers a vanishing mean of nonnegative
numbers to a zero density of events carrying a uniform positive cost. -/
theorem fraction_tendsto_zero_of_average {D : ℕ → ℝ} (hD : ∀ n, 0 ≤ D n)
    (p : ℕ → Prop) [DecidablePred p] {delta : ℝ} (hdelta : 0 < delta)
    (hgap : ∀ n, p n → delta ≤ D n)
    (havg : Tendsto (average D) atTop (𝓝 0)) :
    Tendsto (fraction p) atTop (𝓝 0) := by
  have hbound (n : ℕ) : fraction p n ≤ (1/delta)*average D n := by
    have hsum : delta*(((Finset.range n).filter p).card : ℝ) ≤
        ∑ j in Finset.range n,D j := by
      calc
        delta*(((Finset.range n).filter p).card : ℝ) =
            ∑ j in (Finset.range n).filter p,delta := by simp [mul_comm]
        _ ≤ ∑ j in (Finset.range n).filter p,D j :=
          Finset.sum_le_sum (fun j hj => hgap j (Finset.mem_filter.mp hj).2)
        _ ≤ ∑ j in Finset.range n,D j := Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _) (fun j _ _ => hD j)
    have hcard : (((Finset.range n).filter p).card : ℝ) ≤
        (∑ j in Finset.range n,D j)/delta :=
      (le_div_iff hdelta).2 (by nlinarith only [hsum])
    have h := div_le_div_of_nonneg_right hcard (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    calc
      fraction p n ≤ (∑ j in Finset.range n,D j)/delta/(n : ℝ) := h
      _ = (1/delta)*average D n := by unfold average; ring
  apply squeeze_zero (fun n => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hbound
  simpa only [mul_zero] using (tendsto_const_nhds (x := 1/delta)).mul havg

/-- Vanishing average endpoint defect makes the proportion of reciprocal steps
outside every fixed midpoint neighborhood tend to zero. -/
theorem midpoint_density_zero {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (tau : ℕ → ℝ) (hta : ∀ n, a < tau n) (htb : ∀ n, tau n < b)
    (havg : Tendsto (average (fun n => BB.endpointDefect a b (tau n))) atTop (𝓝 0))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fraction (fun n => epsilon ≤ |tau n-(a+b)/2|)) atTop (𝓝 0) := by
  obtain ⟨delta,hdelta,hgap⟩ := endpointDefect_gap ha hab hepsilon
  exact fraction_tendsto_zero_of_average
    (fun n => BB.endpointDefect_nonneg ha (hta n) (htb n)) _ hdelta
    (fun n hn => hgap _ (hta n) (htb n) hn) havg

/-- Full asymptotic extremality of the actual endpoint energy forces midpoint
concentration. The assertion uses a full root limit, not merely a limsup. -/
theorem midpoint_density_of_extremal_root_limit {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (tau E : ℕ → ℝ) (hta : ∀ n, a < tau n) (htb : ∀ n, tau n < b)
    (hE : 0 < E 0)
    (hstep : ∀ n, E (n+1)=BB.endpointRate a b^2*
      Real.exp (-2*BB.endpointDefect a b (tau n))*E n)
    (hroot : Tendsto (rootEnergy E) atTop (𝓝 (BB.endpointRate a b^2)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (fraction (fun n => epsilon ≤ |tau n-(a+b)/2|)) atTop (𝓝 0) := by
  apply midpoint_density_zero ha hab tau hta htb _ hepsilon
  exact average_zero_of_extremal_root_limit (BB.endpointRate_pos ha hab) hE hstep hroot

end BB.Defect
