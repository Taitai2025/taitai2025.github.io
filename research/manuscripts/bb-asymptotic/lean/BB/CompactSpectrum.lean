import BB.Endpoint
import Mathlib.Topology.Algebra.Order.Compact

/-! # Endpoint data are consequences of compact positive spectral sets -/

noncomputable section
namespace BB
open Set

theorem compact_positive_spectral_endpoints (K : Set ℝ) (hK : IsCompact K)
    (hne : K.Nonempty) (hpos : K ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ IsLeast K a ∧ IsGreatest K b ∧ K ⊆ Icc a b := by
  obtain ⟨a,ha⟩ := hK.exists_isLeast hne
  obtain ⟨b,hb⟩ := hK.exists_isGreatest hne
  exact ⟨a,b,hpos ha.1,ha.2 hb.1,ha,hb,fun _ hx => ⟨ha.2 hx,hb.2 hx⟩⟩

theorem compact_positive_nontrivial_endpoints (K : Set ℝ) (hK : IsCompact K)
    (hK₂ : K.Nontrivial) (hpos : K ⊆ Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ IsLeast K a ∧ IsGreatest K b ∧ K ⊆ Icc a b := by
  obtain ⟨a,b,ha,hab,hlo,hhi,hbounds⟩ := compact_positive_spectral_endpoints K hK hK₂.nonempty hpos
  refine ⟨a,b,ha,?_,hlo,hhi,hbounds⟩
  apply lt_of_le_of_ne hab
  intro he
  obtain ⟨x,hx,y,hy,hxy⟩ := hK₂
  have hx' : x = a := le_antisymm (by simpa only [← he] using (hbounds hx).2) (hbounds hx).1
  have hy' : y = a := le_antisymm (by simpa only [← he] using (hbounds hy).2) (hbounds hy).1
  exact hxy (hx'.trans hy'.symm)

theorem compact_positive_extrema_values (K : Set ℝ) (hK : IsCompact K)
    (hne : K.Nonempty) (hpos : K ⊆ Ioi 0) :
    0 < sInf K ∧ IsLeast K (sInf K) ∧ IsGreatest K (sSup K) ∧
      0 ≤ rate (sInf K) (sSup K) ∧ rate (sInf K) (sSup K) < 1 := by
  obtain ⟨a,b,ha,hab,hlo,hhi,_⟩ := compact_positive_spectral_endpoints K hK hne hpos
  rw [hlo.csInf_eq,hhi.csSup_eq]
  exact ⟨ha,hlo,hhi,div_nonneg (sub_nonneg.mpr hab) (by linarith),rate_lt_one ha hab⟩

end BB
