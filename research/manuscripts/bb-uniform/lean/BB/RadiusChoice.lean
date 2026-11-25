import Mathlib.Topology.Instances.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace BB.RadiusChoice
open Filter Set
open scoped Topology

/-- A one-sided modulus limit provides a positive bootstrap radius below any
prescribed cap. The dilation is positive, so no assumption on `omega 0` is needed. -/
theorem exists_radius_below (omega : ℝ → ℝ)
    (hlim : Tendsto omega (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    {B D c gamma R cap : ℝ} (hB : 0 < B) (hR : 0 < R)
    (hcap : 0 < cap) (hcg : c < gamma) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon < cap ∧ B*epsilon < R ∧
      c+D*omega (B*epsilon) ≤ gamma := by
  have hf : Tendsto (fun t => c+D*omega t) (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds c) := by
    have hh : Tendsto (fun t : ℝ => c+D*omega t) (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (c+D*0)) := tendsto_const_nhds.add (tendsto_const_nhds.mul hlim)
    simpa only [mul_zero,add_zero] using hh
  have hgood : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), c+D*omega t < gamma :=
    hf.eventually (gt_mem_nhds hcg)
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), 0 < t := self_mem_nhdsWithin
  have hsmall : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < R :=
    (gt_mem_nhds hR).filter_mono nhdsWithin_le_nhds
  have hcap' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Ioi 0), t < cap*B :=
    (gt_mem_nhds (mul_pos hcap hB)).filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htpos,htcap,htsmall,htgood⟩ := (hpos.and (hcap'.and (hsmall.and hgood))).exists
  have heq : B*(t/B) = t := by field_simp
  refine ⟨t/B,div_pos htpos hB,(div_lt_iff hB).mpr htcap,?_,?_⟩
  · simpa only [heq] using htsmall
  · simpa only [heq] using htgood.le

/-- Positive bootstrap radius with simultaneous domain and strict-rate margins. -/
theorem exists_radius (omega : ℝ → ℝ)
    (hlim : Tendsto omega (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    {B D c gamma R : ℝ} (hB : 0 < B) (hR : 0 < R) (hcg : c < gamma) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ B*epsilon < R ∧
      c+D*omega (B*epsilon) ≤ gamma := by
  obtain ⟨epsilon,hepsilon,_,hsmall,hgood⟩ :=
    exists_radius_below omega hlim hB hR (show (0 : ℝ) < 1 by norm_num) hcg
  exact ⟨epsilon,hepsilon,hsmall,hgood⟩

/-- A local Hessian modulus can be made at most half the positive coercivity
constant while remaining strictly inside the original neighborhood. -/
theorem exists_coercivity_radius (omega : ℝ → ℝ)
    (hlim : Tendsto omega (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    ∃ R : ℝ, 0 < R ∧ R < r ∧ omega R ≤ a/2 := by
  have hh := exists_radius (B := 1) (D := 1) (c := 0) (gamma := a/2)
    omega hlim (by norm_num) hr (by linarith only [ha])
  simpa only [one_mul,zero_add] using hh

end BB.RadiusChoice
