import BB.CounterexampleDini
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # A global C² extension of the local counterexample

A product of two scalar smooth cutoffs equals one throughout the entire
counterexample rectangle and vanishes before the logarithmic singularities.
Consequently all local objectives, derivatives and orbits are preserved.
-/

noncomputable section
namespace BB.Counterexample
open Set Filter Metric
open scoped Topology

/-- The original coordinate domain is open. -/
theorem constructionDomain_isOpen (sigma : ℝ) : IsOpen (constructionDomain sigma) := by
  exact (isOpen_Ioo.preimage continuous_fst).inter
    (isOpen_Ioo.preimage (continuous_snd.div_const sigma))

private theorem cutoff_zero_near (phi : ContDiffBump (0 : ℝ))
    (q : ℝ × ℝ → ℝ) (hq : Continuous q) {z : ℝ × ℝ}
    (hz : phi.rOut < |q z|) :
    (fun w => phi (q w)) =ᶠ[𝓝 z] (fun _ => 0) := by
  have he : ∀ᶠ w in 𝓝 z, phi.rOut < |q w| :=
    (continuous_abs.comp hq).continuousAt.eventually (lt_mem_nhds hz)
  filter_upwards [he] with w hw
  apply phi.zero_of_le_dist
  simpa only [dist_zero_right,Real.norm_eq_abs] using hw.le

/-- Every C² function on the original logarithmic domain admits a globally C²
extension agreeing with it on any strictly smaller counterexample rectangle. -/
theorem exists_global_c2_extension (F : ℝ × ℝ → ℝ) (sigma : ℝ)
    (hF : ContDiffOn ℝ 2 F (constructionDomain sigma))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∃ Fext : ℝ × ℝ → ℝ, ContDiff ℝ 2 Fext ∧
      EqOn Fext F (smallRectangle sigma r) := by
  let phi : ContDiffBump (0 : ℝ) := {
    rIn := r
    rOut := (r+1)/2
    rIn_pos := hr
    rIn_lt_rOut := by linarith only [hr1] }
  let Fext := fun z : ℝ × ℝ => phi z.1*phi (z.2/sigma)*F z
  have hphi1 : ContDiff ℝ 2 (fun z : ℝ × ℝ => phi z.1) := phi.contDiff.comp contDiff_fst
  have hphi2 : ContDiff ℝ 2 (fun z : ℝ × ℝ => phi (z.2/sigma)) :=
    phi.contDiff.comp (contDiff_snd.div_const sigma)
  have hphiOut : phi.rOut < 1 := by dsimp [phi]; linarith only [hr1]
  refine ⟨Fext,?_,?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ constructionDomain sigma
    · exact (hphi1.contDiffAt.mul hphi2.contDiffAt).mul
        (hF.contDiffAt ((constructionDomain_isOpen sigma).mem_nhds hz))
    · by_cases hu : |z.1| < 1
      · have hv : 1 ≤ |z.2/sigma| := by
          apply le_of_not_gt
          intro hv
          exact hz ⟨abs_lt.mp hu,abs_lt.mp hv⟩
        have he := cutoff_zero_near phi (fun w : ℝ × ℝ => w.2/sigma)
          (continuous_snd.div_const sigma) (hphiOut.trans_le hv)
        apply (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (0 : ℝ)) z).congr_of_eventuallyEq
        filter_upwards [he] with w hw
        simp [Fext,hw]
      · have hv : 1 ≤ |z.1| := le_of_not_gt hu
        have he := cutoff_zero_near phi (fun w : ℝ × ℝ => w.1) continuous_fst
          (hphiOut.trans_le hv)
        apply (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : ℝ × ℝ => (0 : ℝ)) z).congr_of_eventuallyEq
        filter_upwards [he] with w hw
        simp [Fext,hw]
  · intro z hz
    have h1 : phi z.1=1 := phi.one_of_mem_closedBall (by
      simpa [mem_closedBall,dist_zero_right,Real.norm_eq_abs,phi] using hz.1.le)
    have h2 : phi (z.2/sigma)=1 := phi.one_of_mem_closedBall (by
      simpa [mem_closedBall,dist_zero_right,Real.norm_eq_abs,phi,abs_div] using hz.2.le)
    simp [Fext,h1,h2]

/-- Equality on the open rectangle preserves the genuine objective differential. -/
theorem extension_fderiv_eq {Fext F : ℝ × ℝ → ℝ} {sigma r : ℝ}
    (heq : EqOn Fext F (smallRectangle sigma r)) {z : ℝ × ℝ}
    (hz : z ∈ smallRectangle sigma r) : fderiv ℝ Fext z=fderiv ℝ F z := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [(smallRectangle_isOpen sigma r).mem_nhds hz] with w hw
  exact heq hw

/-- The explicit Euclidean strong-convexity inequality is unchanged by extension. -/
theorem strongConvex_extension {Fext F : ℝ × ℝ → ℝ} {sigma r m : ℝ}
    (heq : EqOn Fext F (smallRectangle sigma r))
    (hstrong : EuclideanStrongConvexOn (smallRectangle sigma r) m F) :
    EuclideanStrongConvexOn (smallRectangle sigma r) m Fext := by
  intro x hx y hy t ht ht1
  have hmix : (t*x.1+(1-t)*y.1,t*x.2+(1-t)*y.2) ∈ smallRectangle sigma r :=
    (smallRectangle_convex sigma r) hx hy ht (by linarith only [ht1]) (by ring)
  rw [heq hx,heq hy,heq hmix]
  exact hstrong x hx y hy t ht ht1

end BB.Counterexample
