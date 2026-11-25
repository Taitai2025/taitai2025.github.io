import BB.NonlinearTracking

/-! # Exact invariance of actual BB trajectories under translation -/

noncomputable section
namespace BB.Nonlinear

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem bbState_translate (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbState rule G (a + p) (a + x) n =
      (a + (bbState rule (fun z => G (a + z)) p x n).1,
       a + (bbState rule (fun z => G (a + z)) p x n).2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bbState, bbTransition, ih, add_sub_add_left_eq_sub]
    congr 1
    abel

theorem bbCurrent_translate (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbCurrent rule G (a + p) (a + x) n =
      a + bbCurrent rule (fun z => G (a + z)) p x n :=
  congrArg Prod.snd (bbState_translate rule G a p x n)

theorem bbPrevious_translate (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbPrevious rule G (a + p) (a + x) n =
      a + bbPrevious rule (fun z => G (a + z)) p x n :=
  congrArg Prod.fst (bbState_translate rule G a p x n)

theorem bbStep_translate (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbStep rule G (a + p) (a + x) n = bbStep rule (fun z => G (a + z)) p x n := by
  simp only [bbStep, bbCurrent_translate, bbPrevious_translate, add_sub_add_left_eq_sub]

theorem bbCurrent_center (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbCurrent rule (fun z => G (a + z)) (p - a) (x - a) n = bbCurrent rule G p x n - a := by
  have hh := bbCurrent_translate rule G a (p - a) (x - a) n
  have hp : a + (p - a) = p := by abel
  have hx : a + (x - a) = x := by abel
  rw [hp, hx] at hh
  rw [hh]
  abel

theorem bbPrevious_center (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbPrevious rule (fun z => G (a + z)) (p - a) (x - a) n = bbPrevious rule G p x n - a := by
  have hh := bbPrevious_translate rule G a (p - a) (x - a) n
  have hp : a + (p - a) = p := by abel
  have hx : a + (x - a) = x := by abel
  rw [hp, hx] at hh
  rw [hh]
  abel

theorem bbStep_center (rule : Rule) (G : E → E) (a p x : E) (n : ℕ) :
    bbStep rule (fun z => G (a + z)) (p - a) (x - a) n = bbStep rule G p x n := by
  have hh := bbStep_translate rule G a (p - a) (x - a) n
  have hp : a + (p - a) = p := by abel
  have hx : a + (x - a) = x := by abel
  rw [hp, hx] at hh
  exact hh.symm

theorem strict_derivative_translate (G : E → E) (A : E →L[ℝ] E) (a : E)
    (h : HasStrictFDerivAt G A a) : HasStrictFDerivAt (fun z => G (a + z)) A 0 := by
  have htrans : HasStrictFDerivAt (fun z : E => a + z) (ContinuousLinearMap.id ℝ E) 0 := by
    simpa using (hasStrictFDerivAt_id (𝕜 := ℝ) (0 : E)).const_add a
  have h' : HasStrictFDerivAt G A (a + 0) := by simpa using h
  simpa only [ContinuousLinearMap.comp_id] using h'.comp 0 htrans

theorem gradient_translate [CompleteSpace E] (F : E → ℝ) (G : E → E) (a x : E)
    (h : HasGradientAt F (G (a + x)) (a + x)) :
    HasGradientAt (fun z => F (a + z)) (G (a + x)) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have htrans : HasFDerivAt (fun z : E => a + z) (ContinuousLinearMap.id ℝ E) x := by
    simpa using (hasFDerivAt_id (𝕜 := ℝ) x).const_add a
  simpa only [ContinuousLinearMap.comp_id] using h.hasFDerivAt.comp x htrans

end BB.Nonlinear
