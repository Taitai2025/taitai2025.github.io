import BB.FiniteCompression
import BB.NonlinearTracking

/-! # Exact finite compression of frozen BB1 and BB2 point trajectories -/

namespace BB.Nonlinear
noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem quotient_subtype (rule : Rule) (V : Submodule ℝ E) (s y : V) :
    rule.quotient s y = rule.quotient (s : E) (y : E) := by
  cases rule <;> rfl

theorem compression_frozen_quotient (rule : Rule) (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (s : V) (hs : A (s : E) ∈ V) :
    frozenQuotient rule (operatorCompression A V) s = frozenQuotient rule A (s : E) := by
  have he : (operatorCompression A V s : E) = A (s : E) :=
    orthogonalProjection_eq_self_iff.mpr hs
  unfold frozenQuotient
  rw [quotient_subtype,he]

theorem compression_frozen_next (rule : Rule) (A : E →L[ℝ] E) (V : Submodule ℝ E)
    [HasOrthogonalProjection V] (p x : V)
    (hp : A (p : E) ∈ V) (hx : A (x : E) ∈ V) :
    ((x-frozenQuotient rule (operatorCompression A V) (x-p) • operatorCompression A V x : V) : E) =
      (x : E)-frozenQuotient rule A ((x : E)-(p : E)) • A (x : E) := by
  have hs : A ((x-p : V) : E) ∈ V := by
    change A ((x : E)-(p : E)) ∈ V
    rw [map_sub]
    exact V.sub_mem hx hp
  have he : (operatorCompression A V x : E) = A (x : E) :=
    orthogonalProjection_eq_self_iff.mpr hx
  change (x : E)-frozenQuotient rule (operatorCompression A V) (x-p) •
    (operatorCompression A V x : E) = _
  rw [compression_frozen_quotient rule A V (x-p) hs,he]
  rfl

def frozenTrace (rule : Rule) (A : E →L[ℝ] E) (p x : E) : ℕ → E
  | 0 => p
  | n+1 => bbCurrent rule A p x n

abbrev frozenCompressionSpace (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N : ℕ) :=
  trajectorySpace A (frozenTrace rule A p x) (N+1)

theorem frozen_previous_mem (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N : ℕ) :
    p ∈ frozenCompressionSpace rule A p x N :=
  gradient_mem_trajectorySpace A (frozenTrace rule A p x) (N+1) 0 (by omega)

theorem frozen_current_mem (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N j : ℕ) (hj : j ≤ N+1) :
    bbCurrent rule A p x j ∈ frozenCompressionSpace rule A p x N :=
  gradient_mem_trajectorySpace A (frozenTrace rule A p x) (N+1) (j+1) (by omega)

theorem frozen_current_image_mem (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N j : ℕ) (hj : j ≤ N+1) :
    A (bbCurrent rule A p x j) ∈ frozenCompressionSpace rule A p x N :=
  image_mem_trajectorySpace A (frozenTrace rule A p x) (N+1) (j+1) (by omega)

theorem frozen_previous_image_mem (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N j : ℕ) (hj : j ≤ N+1) :
    A (bbPrevious rule A p x j) ∈ frozenCompressionSpace rule A p x N := by
  cases j with
  | zero => exact image_mem_trajectorySpace A (frozenTrace rule A p x) (N+1) 0 (by omega)
  | succ j =>
    rw [bbPrevious_succ]
    exact frozen_current_image_mem rule A p x N j (by omega)

def frozenCompressionPrevious (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N : ℕ) :
    frozenCompressionSpace rule A p x N :=
  ⟨p,frozen_previous_mem rule A p x N⟩

def frozenCompressionInitial (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N : ℕ) :
    frozenCompressionSpace rule A p x N :=
  ⟨x,frozen_current_mem rule A p x N 0 (by omega)⟩

/-- Both entries of the actual frozen state agree exactly through the horizon.
This proof covers BB1, BB2, zero secants, and termination without extra domain
assumptions; the separate localization theorem proves legitimacy before hitting. -/
theorem frozen_compression_matches (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N : ℕ) :
    ∀ j, j ≤ N →
      ((bbPrevious rule (operatorCompression A (frozenCompressionSpace rule A p x N))
        (frozenCompressionPrevious rule A p x N) (frozenCompressionInitial rule A p x N) j :
          frozenCompressionSpace rule A p x N) : E) = bbPrevious rule A p x j ∧
      ((bbCurrent rule (operatorCompression A (frozenCompressionSpace rule A p x N))
        (frozenCompressionPrevious rule A p x N) (frozenCompressionInitial rule A p x N) j :
          frozenCompressionSpace rule A p x N) : E) = bbCurrent rule A p x j := by
  let V := frozenCompressionSpace rule A p x N
  let B := operatorCompression A V
  let pV := frozenCompressionPrevious rule A p x N
  let xV := frozenCompressionInitial rule A p x N
  change ∀ j, j ≤ N →
    ((bbPrevious rule B pV xV j : V) : E) = bbPrevious rule A p x j ∧
    ((bbCurrent rule B pV xV j : V) : E) = bbCurrent rule A p x j
  intro j
  induction j with
  | zero => intro _; exact ⟨rfl,rfl⟩
  | succ j ih =>
    intro hj
    have hh := ih (by omega)
    have hp : A ((bbPrevious rule B pV xV j : V) : E) ∈ V := by
      rw [hh.1]
      exact frozen_previous_image_mem rule A p x N j (by omega)
    have hx : A ((bbCurrent rule B pV xV j : V) : E) ∈ V := by
      rw [hh.2]
      exact frozen_current_image_mem rule A p x N j (by omega)
    constructor
    · rw [bbPrevious_succ,bbPrevious_succ]
      exact hh.2
    · rw [bbCurrent_succ,bbCurrent_succ,quadratic_bbStep,quadratic_bbStep]
      have hnext := compression_frozen_next rule A V (bbPrevious rule B pV xV j)
        (bbCurrent rule B pV xV j) hp hx
      rw [hh.1,hh.2] at hnext
      exact hnext

theorem frozen_compression_norm (rule : Rule) (A : E →L[ℝ] E) (p x : E) (N j : ℕ) (hj : j ≤ N) :
    ‖bbCurrent rule (operatorCompression A (frozenCompressionSpace rule A p x N))
      (frozenCompressionPrevious rule A p x N) (frozenCompressionInitial rule A p x N) j‖ =
        ‖bbCurrent rule A p x j‖ :=
  congrArg norm (frozen_compression_matches rule A p x N j hj).2

end
end BB.Nonlinear
