import BB.EuclideanMaps

/-! # The literal finite-horizon Euclidean Lyapunov candidate

This module packages the original candidate with its exact coefficient.
The actual boundary contraction is proved in `EuclideanRecursion`.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean.System
open BB.Gluing

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (s : System E Ω)

/-- The manuscript's literal `V_construct`, using its recursive N and K=A. -/
def candidate (lo hi : Fin (s.n+2)) : Pair E → ℝ :=
  V (s.scaled (s.faceRate lo hi)) (s.faceLength lo hi)
    (s.facePrefactor lo hi) (s.endpoint lo hi)

/-- Both the candidate and its prefactor are fixed, rather than existentially
chosen substitutes. -/
def LiteralCertificate (lo hi : Fin (s.n+2)) :=
  {v : Certificate s.step (s.domain lo hi) (s.faceRate lo hi) //
    v.value=s.candidate lo hi ∧ v.prefactor=s.facePrefactor lo hi}

theorem literal_certificate_of_boundary {lo hi : Fin (s.n+2)} (hlohi : lo<hi)
    (hboundary : ∀ l : List Ω, l.length=s.faceLength lo hi → ∀ z ∈ s.domain lo hi,
      s.endpoint lo hi z=0 →
      ‖run (s.scaled (s.faceRate lo hi)) l z‖≤(1/2 : ℝ)*‖z‖) :
    Nonempty (s.LiteralCertificate lo hi) := by
  have hc := s.faceRate_pos hlohi
  have hΛ : 1≤s.L/s.faceRate lo hi :=
    (one_le_div hc).mpr ((s.faceRate_lt_one hlohi).le.trans s.L_ge_one)
  have hN : 1<s.faceLength lo hi := by have hh := s.faceLength_ge_three hlohi; omega
  have hS := fun (w : Ω) (z : Pair E) (hz : z ∈ s.domain lo hi) =>
    s.scaled_mem (s.faceRate lo hi) w hz
  have hbound := fun (w : Ω) (z : Pair E) (hz : z ∈ s.domain lo hi) =>
    s.scaled_bound hc w hz.1
  have hPbound := fun (z : Pair E) (_ : z ∈ s.domain lo hi) =>
    P_le_norm s.symmetric s.card (s.lam_pos lo) hlohi z
  obtain ⟨v,hv⟩ := finite_horizon_certificate hc.le hΛ hN
    (fun z hz t _ => s.domain_scale hz t) hS
    (fun w z _ => s.step_eq_scale_scaled hc.ne' w z) hbound
    (fun w x y hx hy => s.scaled_lipschitz hc w hx.1 hy.1)
    (fun w z _ t _ => s.scaled_smul (s.faceRate lo hi) w z t)
    (fun w z hz => s.endpoint_scaled_step hlohi w hz)
    hPbound
    (fun z _ t ht => P_homogeneous s.symmetric s.card (s.lam_pos lo) hlohi z ht)
    (by
      intro z hz
      obtain ⟨z',hz',_,hp,hn,hd⟩ := endpoint_deletion s.symmetric s.card (s.lam_pos lo) hlohi hz
      exact ⟨z',hz',hp,hn,hd⟩)
    hboundary
    (by
      intro A hA
      obtain ⟨J,hJ,hLip⟩ := Q_regular s.symmetric s.card (s.lam_pos lo) hlohi hA
      exact ⟨J,hJ,fun x y _ _ => hLip x y⟩)
  have hu : ∀ z ∈ s.domain lo hi, v.value z≤s.facePrefactor lo hi*‖z‖ := by
    intro z hz
    rw [hv,s.facePrefactor_eq hlohi]
    exact V_upper (by omega) hΛ hS hbound hPbound hz
  let v' : Certificate s.step (s.domain lo hi) (s.faceRate lo hi) :=
    { v with
      prefactor := s.facePrefactor lo hi
      prefactor_ge_one := s.facePrefactor_ge_one hlohi
      upper := hu }
  refine ⟨⟨v',?_,rfl⟩⟩
  change v.value=s.candidate lo hi
  rw [hv,candidate,s.facePrefactor_eq hlohi]

/-- The two-eigenvalue base: the vanishing endpoint is removed on the first
step, and the actual singleton dynamics terminate on the next two steps. -/
theorem boundary_adjacent {lo hi : Fin (s.n+2)} (hlohi : lo<hi)
    (hadj : hi.val=lo.val+1) (l : List Ω) (hl : l.length=3)
    {z : Pair E} (hz : z ∈ s.domain lo hi) (hp : s.endpoint lo hi z=0) :
    ‖run (s.scaled (s.faceRate lo hi)) l z‖≤(1/2 : ℝ)*‖z‖ := by
  cases l with
  | nil => simp at hl
  | cons w l =>
    cases l with
    | nil => simp at hl
    | cons w' l =>
      cases l with
      | nil => simp at hl
      | cons w'' l =>
        have hl0 : l=[] := by apply List.length_eq_zero.mp; simp only [List.length_cons] at hl; omega
        subst l
        have hh := boundary_handoff s.symmetric s.card (s.lam_pos lo) hlohi hadj hadj.symm
          hz hp (s.step_cone w hz.1)
        have hnil : s.step w'' (s.step w' (s.scaled (s.faceRate lo hi) w z))=0 := by
          rcases hh with hh | hh
          · exact singleton_two_updates s.symmetric s.card (s.lam_pos hi) (s.weight_positive w')
              (stateSet_smul s.symmetric s.card hh (s.faceRate lo hi)⁻¹)
          · exact singleton_two_updates s.symmetric s.card (s.lam_pos lo) (s.weight_positive w')
              (stateSet_smul s.symmetric s.card hh (s.faceRate lo hi)⁻¹)
        change ‖(s.faceRate lo hi)⁻¹ • s.step w''
          ((s.faceRate lo hi)⁻¹ • s.step w' (s.scaled (s.faceRate lo hi) w z))‖≤(1/2 : ℝ)*‖z‖
        rw [s.step_smul,hnil,smul_zero,smul_zero,norm_zero]
        positivity

end BB.Euclidean.System
