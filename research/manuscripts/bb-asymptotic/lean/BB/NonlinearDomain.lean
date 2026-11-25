import BB.NonlinearMain
import BB.NonlinearAssumptions

/-!
# The open local domain and independence from extensions

The source's local functions are represented in mathlib by ambient functions
with derivative assumptions on an open set.  The selected closed ball is proved
to lie in that set.  A separate exact recurrence identity shows that arbitrary
values outside the domain cannot affect a trajectory that stays inside it.
-/

noncomputable section
namespace BB.Nonlinear
open Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem nonlinear_localization_on_open_set (rule : Rule) (F : E → ℝ) (G : E → E)
    (U : Set E) (hU : IsOpen U) (a : E) (haU : a ∈ U)
    (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (m M γ : ℝ)
    (hm : 0 < m) (hmM : m ≤ M)
    (hbounds : ∀ z : E, m*‖z‖^2 ≤ inner (𝕜 := ℝ) z (A z) ∧
      inner (𝕜 := ℝ) z (A z) ≤ M*‖z‖^2)
    (hG : G a = 0) (hstrict : HasStrictFDerivAt G A a)
    (hγ : BB.rate m M < γ) (hγ1 : γ < 1)
    (hgrad : ∀ z ∈ U, HasGradientWithinAt F (G z) U z) :
    ∃ R > 0, Metric.closedBall a R ⊆ U ∧
      LocalGuarantee rule F G a (BB.rate m M) γ R := by
  obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds haU)
  let R := d/2
  have hR : 0 < R := div_pos hd (by norm_num)
  have hRU : Metric.closedBall a R ⊆ U := by
    intro z hz
    apply hdU
    exact (Metric.mem_closedBall.mp hz).trans_lt (half_lt_self hd)
  refine ⟨R,hR,hRU,?_⟩
  apply nonlinear_localization rule F G a A hA m M γ R hm hmM hbounds hG hstrict hγ hγ1 hR
  intro z hz
  have hzU : z ∈ U := hRU (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)
  exact hasGradientAt_iff_hasFDerivAt.mpr
    ((hgrad z hzU).hasFDerivWithinAt.hasFDerivAt (hU.mem_nhds hzU))

theorem bbState_eq_of_eqOn_on_orbit (rule : Rule) (G H : E → E) (U : Set E)
    (hGH : EqOn G H U) (p x : E) (hp : p ∈ U)
    (hstay : ∀ n, bbCurrent rule G p x n ∈ U) :
    ∀ n, bbState rule G p x n = bbState rule H p x n := by
  have hprev : ∀ n, bbPrevious rule G p x n ∈ U := by
    intro n
    cases n with
    | zero => exact hp
    | succ n => simpa only [bbPrevious_succ] using hstay n
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change bbTransition rule G (bbState rule G p x n) =
      bbTransition rule H (bbState rule H p x n)
    rw [← ih]
    have hcur := hGH (hstay n)
    have hpr := hGH (hprev n)
    unfold bbTransition
    change ((bbState rule G p x n).2, _) = ((bbState rule G p x n).2, _)
    change G ((bbState rule G p x n).2) = H ((bbState rule G p x n).2) at hcur
    change G ((bbState rule G p x n).1) = H ((bbState rule G p x n).1) at hpr
    simp only [hcur,hpr]

end BB.Nonlinear
