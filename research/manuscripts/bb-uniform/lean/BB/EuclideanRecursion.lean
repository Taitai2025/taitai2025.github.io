import BB.EuclideanConstruction
import BB.EuclideanFaceConstants

/-! # The original recursive Euclidean N, V and K are valid

The induction is over the number of actual distinct eigenvalues in an
interval.  Every boundary estimate is derived from the actual commuting
weighted quotient map and the already constructed child certificates.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean.System
open BB.Gluing

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (s : System E Ω)

theorem boundary_recursive {lo hi next prev : Fin (s.n+2)}
    (hnext : next.val=lo.val+1) (hprev : prev.val+1=hi.val)
    (hspan : 2≤hi.val-lo.val)
    (v₁ : s.LiteralCertificate next hi) (v₂ : s.LiteralCertificate lo prev)
    (l : List Ω) (hl : l.length=s.faceLength lo hi)
    {z : Pair E} (hz : z ∈ s.domain lo hi) (hp : s.endpoint lo hi z=0) :
    ‖run (s.scaled (s.faceRate lo hi)) l z‖≤(1/2 : ℝ)*‖z‖ := by
  have hlohi : lo<hi := by change lo.val<hi.val; omega
  have hnh : next<hi := by change next.val<hi.val; omega
  have hlp : lo<prev := by change lo.val<prev.val; omega
  have hc := s.faceRate_pos hlohi
  have hc₁ := s.faceRate_pos hnh
  have hc₂ := s.faceRate_pos hlp
  let K := max (s.facePrefactor next hi) (s.facePrefactor lo prev)
  let r := max (s.faceRate next hi) (s.faceRate lo prev)/s.faceRate lo hi
  have hK : 0≤K :=
    (zero_le_one.trans (s.facePrefactor_ge_one hnh)).trans (le_max_left _ _)
  have hr : 0≤r := (s.childRatio_pos_lt_one hnext hprev hspan).1.le
  have hN := s.faceLength_ge_three hlohi
  cases l with
  | nil => simp at hl; omega
  | cons w l =>
    have hlen : l.length=s.faceLength lo hi-1 := by simp only [List.length_cons] at hl; omega
    have hh := boundary_handoff s.symmetric s.card (s.lam_pos lo) hlohi hnext hprev
      hz hp (s.step_cone w hz.1)
    have htail : ‖run (s.scaled (s.faceRate lo hi)) l
        (s.scaled (s.faceRate lo hi) w z)‖≤K*r^l.length*‖s.scaled (s.faceRate lo hi) w z‖ := by
      rcases hh with hh | hh
      · have hm := stateSet_smul s.symmetric s.card hh (s.faceRate lo hi)⁻¹
        have hb := s.rescaled_word_bound v₁.val hc₁.le hc l hm
        rw [v₁.property.2] at hb
        have hpow : (s.faceRate next hi/s.faceRate lo hi)^l.length≤r^l.length :=
          pow_le_pow_left (div_nonneg hc₁.le hc.le)
            (div_le_div_of_nonneg_right (le_max_left _ _) hc.le) _
        have hmul : s.facePrefactor next hi*(s.faceRate next hi/s.faceRate lo hi)^l.length≤K*r^l.length :=
          mul_le_mul (le_max_left _ _) hpow (pow_nonneg (div_nonneg hc₁.le hc.le) _) hK
        exact hb.trans (mul_le_mul_of_nonneg_right hmul (norm_nonneg _))
      · have hm := stateSet_smul s.symmetric s.card hh (s.faceRate lo hi)⁻¹
        have hb := s.rescaled_word_bound v₂.val hc₂.le hc l hm
        rw [v₂.property.2] at hb
        have hpow : (s.faceRate lo prev/s.faceRate lo hi)^l.length≤r^l.length :=
          pow_le_pow_left (div_nonneg hc₂.le hc.le)
            (div_le_div_of_nonneg_right (le_max_right _ _) hc.le) _
        have hmul : s.facePrefactor lo prev*(s.faceRate lo prev/s.faceRate lo hi)^l.length≤K*r^l.length :=
          mul_le_mul (le_max_right _ _) hpow (pow_nonneg (div_nonneg hc₂.le hc.le) _) hK
        exact hb.trans (mul_le_mul_of_nonneg_right hmul (norm_nonneg _))
    have hcoeff : (s.B/s.faceRate lo hi)*K*r^l.length≤(1/2 : ℝ) := by
      rw [hlen]
      exact s.boundary_half hnext hprev hspan
    calc
      ‖run (s.scaled (s.faceRate lo hi)) (w::l) z‖≤K*r^l.length*‖s.scaled (s.faceRate lo hi) w z‖ := htail
      _ ≤ K*r^l.length*((s.B/s.faceRate lo hi)*‖z‖) :=
        mul_le_mul_of_nonneg_left (s.scaled_growth hc w hz.1) (mul_nonneg hK (pow_nonneg hr _))
      _ = ((s.B/s.faceRate lo hi)*K*r^l.length)*‖z‖ := by ring
      _ ≤ (1/2 : ℝ)*‖z‖ := mul_le_mul_of_nonneg_right hcoeff (norm_nonneg z)

/-- The full literal recursive construction, at the exact endpoint rate,
for every actual spectral interval.  No child bound or boundary estimate
is assumed: they are discharged by strong induction. -/
theorem literal_interval_certificate (lo hi : Fin (s.n+2)) (hlohi : lo<hi) :
    Nonempty (s.LiteralCertificate lo hi) := by
  have allIntervals : ∀ d : ℕ, ∀ lo hi : Fin (s.n+2), lo<hi → hi.val-lo.val=d →
      Nonempty (s.LiteralCertificate lo hi) := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro lo hi hlohi hd
      by_cases hadj : hi.val=lo.val+1
      · apply s.literal_certificate_of_boundary hlohi
        intro l hl z hz hp
        rw [s.faceLength_adjacent hadj] at hl
        exact s.boundary_adjacent hlohi hadj l hl hz hp
      have hspan : 2≤hi.val-lo.val := by have hlt : lo.val<hi.val := hlohi; omega
      let next : Fin (s.n+2) := ⟨lo.val+1,by omega⟩
      let prev : Fin (s.n+2) := ⟨hi.val-1,by omega⟩
      have hnext : next.val=lo.val+1 := rfl
      have hprev : prev.val+1=hi.val := by dsimp [prev]; omega
      have hnh : next<hi := by change next.val<hi.val; omega
      have hlp : lo<prev := by change lo.val<prev.val; omega
      have hd₁ : hi.val-next.val<d := by omega
      have hd₂ : prev.val-lo.val<d := by omega
      obtain ⟨v₁⟩ := ih _ hd₁ next hi hnh rfl
      obtain ⟨v₂⟩ := ih _ hd₂ lo prev hlp rfl
      apply s.literal_certificate_of_boundary hlohi
      intro l hl z hz hp
      exact s.boundary_recursive hnext hprev hspan v₁ v₂ l hl hz hp
  exact allIntervals _ lo hi hlohi rfl

end BB.Euclidean.System
