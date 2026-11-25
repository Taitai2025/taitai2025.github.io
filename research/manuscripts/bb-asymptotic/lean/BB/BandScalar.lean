import BB.Endpoint
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Compactness.Compact

/-! # Uniform endpoint-band perturbations

The perturbation radius is uniform in all nested spectral intervals, including
degenerate intervals.  Compactness is applied to explicit scalar parameters;
no convergence theorem is assumed.
-/

namespace BB
noncomputable section
open Set

abbrev EndpointDomain (A B : ℝ) :=
  {p : ℝ × ℝ × ℝ // A ≤ p.1 ∧ p.1 ≤ p.2.2 ∧ p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ B}

instance endpointDomainCompact (A B : ℝ) : CompactSpace (EndpointDomain A B) := by
  apply isCompact_iff_compactSpace.mp
  have hc : IsClosed {p : ℝ × ℝ × ℝ |
      A ≤ p.1 ∧ p.1 ≤ p.2.2 ∧ p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ B} :=
    (isClosed_le continuous_const continuous_fst).inter
      ((isClosed_le continuous_fst (continuous_snd.comp continuous_snd)).inter
      ((isClosed_le (continuous_snd.comp continuous_snd)
        (continuous_fst.comp continuous_snd)).inter
      (isClosed_le (continuous_fst.comp continuous_snd) continuous_const)))
  apply (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hc
  intro p hp
  exact ⟨⟨hp.1,hp.2.1.trans (hp.2.2.1.trans hp.2.2.2)⟩,
    ⟨hp.1.trans (hp.2.1.trans hp.2.2.1),hp.2.2.2⟩,
    ⟨hp.1.trans hp.2.1,hp.2.2.1.trans hp.2.2.2⟩⟩

def bandEndpointProduct (A a b u δ : ℝ) : ℝ :=
  ((u-a)/u+δ/A)^(leftWeight a b) * ((b-u)/u+δ/A)^(rightWeight a b)

theorem endpoint_product_le_closed {a b u : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hau : a ≤ u) (hub : u ≤ b) :
    endpointProduct a b u ≤ rate a b := by
  rcases lt_or_eq_of_le hab with hab | hab
  · exact endpoint_product_le ha hab ⟨hau,hub⟩
  · have hua : u = a := le_antisymm (hub.trans hab.symm.le) hau
    subst b
    subst u
    have hp : 0 < leftWeight a a := div_pos ha (by linarith)
    simp only [endpointProduct,sub_self,zero_div,Real.zero_rpow hp.ne',zero_mul,rate]
    simp

theorem band_endpoint_product_continuous (A B : ℝ) (hA : 0 < A) :
    Continuous (fun p : EndpointDomain A B × ℝ =>
      bandEndpointProduct A p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2) := by
  have hca : Continuous (fun p : EndpointDomain A B × ℝ => p.1.1.1) :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
  have hcb : Continuous (fun p : EndpointDomain A B × ℝ => p.1.1.2.1) :=
    (continuous_fst.comp continuous_snd).comp (continuous_subtype_val.comp continuous_fst)
  have hcu : Continuous (fun p : EndpointDomain A B × ℝ => p.1.1.2.2) :=
    (continuous_snd.comp continuous_snd).comp (continuous_subtype_val.comp continuous_fst)
  have hapos : ∀ p : EndpointDomain A B × ℝ, 0 < p.1.1.1 :=
    fun p => hA.trans_le p.1.2.1
  have hbpos : ∀ p : EndpointDomain A B × ℝ, 0 < p.1.1.2.1 :=
    fun p => (hapos p).trans_le (p.1.2.2.1.trans p.1.2.2.2.1)
  have hupos : ∀ p : EndpointDomain A B × ℝ, 0 < p.1.1.2.2 :=
    fun p => (hapos p).trans_le p.1.2.2.1
  have hs : ∀ p : EndpointDomain A B × ℝ, p.1.1.1+p.1.1.2.1 ≠ 0 :=
    fun p => ne_of_gt (add_pos (hapos p) (hbpos p))
  unfold bandEndpointProduct leftWeight rightWeight
  apply Continuous.mul
  · exact (((hcu.sub hca).div hcu (fun p => (hupos p).ne')).add
      (continuous_snd.div_const A)).rpow (hcb.div (hca.add hcb) hs)
      (fun p => Or.inr (div_pos (hbpos p) (add_pos (hapos p) (hbpos p))))
  · exact (((hcb.sub hcu).div hcu (fun p => (hupos p).ne')).add
      (continuous_snd.div_const A)).rpow (hca.div (hca.add hcb) hs)
      (fun p => Or.inr (div_pos (hapos p) (add_pos (hapos p) (hbpos p))))

/-- The same band width and strict contraction factor work for every nested
interval, including a singleton. -/
theorem uniform_endpoint_band_bound (A B γ : ℝ) (hA : 0 < A) (hAB : A ≤ B)
    (hγ : rate A B < γ) :
    ∃ δ ρ : ℝ, 0 < δ ∧ 0 < ρ ∧ ρ < γ ∧
      ∀ a b u : ℝ, A ≤ a → a ≤ u → u ≤ b → b ≤ B →
        bandEndpointProduct A a b u δ ≤ ρ := by
  let ρ : ℝ := (rate A B+γ)/2
  have hc0 : 0 ≤ rate A B := div_nonneg (sub_nonneg.mpr hAB) (by linarith)
  have hcρ : rate A B < ρ := by dsimp [ρ]; linarith
  have hργ : ρ < γ := by dsimp [ρ]; linarith
  let U : Set (EndpointDomain A B × ℝ) :=
    {p | bandEndpointProduct A p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2 < ρ}
  have hU : IsOpen U := isOpen_lt (band_endpoint_product_continuous A B hA) continuous_const
  have hbase : (univ : Set (EndpointDomain A B)) ×ˢ ({0} : Set ℝ) ⊆ U := by
    intro p hp
    have ht : p.2 = 0 := mem_singleton_iff.mp hp.2
    change bandEndpointProduct A p.1.1.1 p.1.1.2.1 p.1.1.2.2 p.2 < ρ
    rw [ht]
    simp only [bandEndpointProduct,zero_div,add_zero]
    have hp0 := p.1.2
    have h1 := endpoint_product_le_closed (hA.trans_le hp0.1)
      (hp0.2.1.trans hp0.2.2.1) hp0.2.1 hp0.2.2.1
    exact (h1.trans (rate_mono_interval hA hp0.1 (hp0.2.1.trans hp0.2.2.1)
      hp0.2.2.2)).trans_lt hcρ
  obtain ⟨V,W,_hV,hW,hall,hzero,hVW⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hU hbase
  have h0W : (0:ℝ) ∈ W := hzero (mem_singleton 0)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hW 0 h0W
  have hδW : ε/2 ∈ W := hball (by
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos (half_pos hε)]
    linarith)
  refine ⟨ε/2,ρ,half_pos hε,hc0.trans_lt hcρ,hργ,?_⟩
  intro a b u hAa hau hub hbB
  let x : EndpointDomain A B := ⟨(a,b,u),hAa,hau,hub,hbB⟩
  have hh : bandEndpointProduct A a b u (ε/2) < ρ :=
    hVW (show (x,ε/2) ∈ V ×ˢ W from ⟨hall (mem_univ x),hδW⟩)
  exact hh.le

theorem lower_band_multiplier_bound {A a u lam δ : ℝ} (hA : 0 < A)
    (hAa : A ≤ a) (hau : a ≤ u) (halam : a ≤ lam) (hlam : lam ≤ a+δ) :
    |1-lam/u| ≤ (u-a)/u+δ/A := by
  have hu : 0 < u := hA.trans_le (hAa.trans hau)
  have hδ : 0 ≤ δ := by linarith
  have hnum : |u-lam| ≤ u-a+δ := by
    calc
      |u-lam| ≤ |u-a|+|a-lam| := abs_sub_le u a lam
      _ = (u-a)+(lam-a) := by rw [abs_of_nonneg (sub_nonneg.mpr hau),abs_of_nonpos (sub_nonpos.mpr halam)]; ring
      _ ≤ u-a+δ := by linarith
  calc
    |1-lam/u| = |u-lam|/u := by rw [← div_self hu.ne',← sub_div,abs_div,abs_of_pos hu]
    _ ≤ (u-a+δ)/u := (div_le_div_right hu).mpr hnum
    _ = (u-a)/u+δ/u := add_div _ _ _
    _ ≤ (u-a)/u+δ/A := add_le_add_left
      (div_le_div_of_nonneg_left hδ hA (hAa.trans hau)) _

theorem upper_band_multiplier_bound {A b u lam δ : ℝ} (hA : 0 < A)
    (hAu : A ≤ u) (hub : u ≤ b) (hlam : b-δ ≤ lam) (hlamb : lam ≤ b) :
    |1-lam/u| ≤ (b-u)/u+δ/A := by
  have hu : 0 < u := hA.trans_le hAu
  have hδ : 0 ≤ δ := by linarith
  have hnum : |u-lam| ≤ b-u+δ := by
    calc
      |u-lam| ≤ |u-b|+|b-lam| := abs_sub_le u b lam
      _ = (b-u)+(b-lam) := by rw [abs_of_nonpos (sub_nonpos.mpr hub),abs_of_nonneg (sub_nonneg.mpr hlamb)]; ring
      _ ≤ b-u+δ := by linarith
  calc
    |1-lam/u| = |u-lam|/u := by rw [← div_self hu.ne',← sub_div,abs_div,abs_of_pos hu]
    _ ≤ (b-u+δ)/u := (div_le_div_right hu).mpr hnum
    _ = (b-u)/u+δ/u := add_div _ _ _
    _ ≤ (b-u)/u+δ/A := add_le_add_left (div_le_div_of_nonneg_left hδ hA hAu) _

end
end BB
