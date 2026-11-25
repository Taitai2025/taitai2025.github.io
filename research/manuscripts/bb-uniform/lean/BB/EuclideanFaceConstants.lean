import BB.EuclideanSystem

/-! # Literal recursive horizons on the finite ordered spectrum

The arithmetic below translates the total natural-index recursion back to
actual adjacent spectral faces.  The boundary estimate uses exactly its child
prefactors and rates, with the original ambient constants B and L.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean.System

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (s : BB.Euclidean.System E Ω)

theorem faceLength_adjacent {lo hi : Fin (s.n+2)} (hadj : hi.val=lo.val+1) :
    s.faceLength lo hi=3 := by
  unfold faceLength
  have hdiff : hi.val-lo.val=1 := by omega
  rw [hdiff,BB.Recursive.length_one]

theorem faceRate_raise_lower {lo next hi : Fin (s.n+2)}
    (hln : lo<next) (hnh : next≤hi) : s.faceRate next hi<s.faceRate lo hi :=
  BB.Faces.rate_raise_lower (s.lam_pos lo) (s.lam_strictMono hln) (s.lam_strictMono.monotone hnh)

theorem faceRate_lower_upper {lo prev hi : Fin (s.n+2)}
    (hlp : lo≤prev) (hph : prev<hi) : s.faceRate lo prev<s.faceRate lo hi :=
  BB.Faces.rate_lower_upper (s.lam_pos lo) (s.lam_strictMono.monotone hlp) (s.lam_strictMono hph)

/-- The exact finite-index counterpart of `BB.Recursive.length_succ_succ`. -/
theorem faceLength_recursive {lo hi next prev : Fin (s.n+2)}
    (hnext : next.val=lo.val+1) (hprev : prev.val+1=hi.val)
    (hspan : 2≤hi.val-lo.val) :
    s.faceLength lo hi=BB.BoundaryExplicit.length s.B
      (max (s.facePrefactor next hi) (s.facePrefactor lo prev)) (s.faceRate lo hi)
      (max (s.faceRate next hi) (s.faceRate lo prev)/s.faceRate lo hi) := by
  let d : ℕ := hi.val-lo.val-2
  have hfull : hi.val-lo.val=d+2 := by dsimp [d]; omega
  have hleft : hi.val-next.val=d+1 := by dsimp [d]; omega
  have hright : prev.val-lo.val=d+1 := by dsimp [d]; omega
  have hlohi : lo≤hi := by change lo.val≤hi.val; omega
  have hnhi : next≤hi := by change next.val≤hi.val; omega
  have hlp : lo≤prev := by change lo.val≤prev.val; omega
  have hKm : BB.Recursive.prefactor (BB.Recursive.extend s.lam) s.B s.L (lo.val+1) (d+1)=
      s.facePrefactor next hi := by
    unfold facePrefactor
    rw [hleft,hnext]
  have hKp : BB.Recursive.prefactor (BB.Recursive.extend s.lam) s.B s.L lo.val (d+1)=
      s.facePrefactor lo prev := by
    unfold facePrefactor
    rw [hright]
  have hcm : BB.Recursive.rate (BB.Recursive.extend s.lam) (lo.val+1) (d+1)=s.faceRate next hi := by
    rw [← hnext,← hleft]
    exact s.natRate_eq hnhi
  have hcp : BB.Recursive.rate (BB.Recursive.extend s.lam) lo.val (d+1)=s.faceRate lo prev := by
    rw [← hright]
    exact s.natRate_eq hlp
  have hc : BB.Recursive.rate (BB.Recursive.extend s.lam) lo.val (d+2)=s.faceRate lo hi := by
    rw [← hfull]
    exact s.natRate_eq hlohi
  calc
    s.faceLength lo hi=BB.Recursive.length (BB.Recursive.extend s.lam) s.B s.L lo.val (d+2) := by
      unfold faceLength
      rw [hfull]
    _ = _ := by rw [BB.Recursive.length_succ_succ,hKm,hKp,hc,hcm,hcp]

theorem childRatio_pos_lt_one {lo hi next prev : Fin (s.n+2)}
    (hnext : next.val=lo.val+1) (hprev : prev.val+1=hi.val)
    (hspan : 2≤hi.val-lo.val) :
    0<max (s.faceRate next hi) (s.faceRate lo prev)/s.faceRate lo hi ∧
      max (s.faceRate next hi) (s.faceRate lo prev)/s.faceRate lo hi<1 := by
  have hlohi : lo<hi := by change lo.val<hi.val; omega
  have hln : lo<next := by change lo.val<next.val; omega
  have hnh : next<hi := by change next.val<hi.val; omega
  have hlp : lo<prev := by change lo.val<prev.val; omega
  have hph : prev<hi := by change prev.val<hi.val; omega
  exact ⟨div_pos ((s.faceRate_pos hnh).trans_le (le_max_left _ _)) (s.faceRate_pos hlohi),
    (div_lt_one (s.faceRate_pos hlohi)).mpr
      (max_lt (s.faceRate_raise_lower hln hnh.le) (s.faceRate_lower_upper hlp.le hph))⟩

/-- The source's exact boundary-half inequality for the recursively specified
finite face.  It contains no replacement or existential child constants. -/
theorem boundary_half {lo hi next prev : Fin (s.n+2)}
    (hnext : next.val=lo.val+1) (hprev : prev.val+1=hi.val)
    (hspan : 2≤hi.val-lo.val) :
    (s.B/s.faceRate lo hi)*max (s.facePrefactor next hi) (s.facePrefactor lo prev)*
      (max (s.faceRate next hi) (s.faceRate lo prev)/s.faceRate lo hi)^
        (s.faceLength lo hi-1)≤1/2 := by
  have hlohi : lo<hi := by change lo.val<hi.val; omega
  have hnh : next<hi := by change next.val<hi.val; omega
  have hK : 0<max (s.facePrefactor next hi) (s.facePrefactor lo prev) :=
    (zero_lt_one.trans_le (s.facePrefactor_ge_one hnh)).trans_le (le_max_left _ _)
  have hratio := s.childRatio_pos_lt_one hnext hprev hspan
  rw [s.faceLength_recursive hnext hprev hspan]
  exact BB.BoundaryExplicit.boundary_length_half
    (zero_lt_one.trans_le s.B_ge_one) hK (s.faceRate_pos hlohi) hratio.1 hratio.2

end BB.Euclidean.System
