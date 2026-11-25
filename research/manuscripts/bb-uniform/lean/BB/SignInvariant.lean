import BB.ScalarSupport
import BB.Gluing
import BB.SpectralFaces

set_option autoImplicit false

namespace BB.Spectral
variable {ι : Type*} [Fintype ι]

noncomputable def absVector (u : ι → ℝ) : ι → ℝ := fun i => |u i|
noncomputable def absState (z : State ι) : State ι := (absVector z.1,absVector z.2)

@[simp] theorem absVector_idempotent (u : ι → ℝ) : absVector (absVector u) = absVector u := by
  funext i
  simp [absVector]

@[simp] theorem absState_idempotent (z : State ι) : absState (absState z) = absState z := by
  simp [absState]

@[simp] theorem absVector_norm (u : ι → ℝ) : ‖absVector u‖ = ‖u‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [absVector,Real.norm_eq_abs,abs_abs] using norm_le_pi_norm u i
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    simpa only [absVector,Real.norm_eq_abs,abs_abs] using norm_le_pi_norm (absVector u) i

@[simp] theorem absState_norm (z : State ι) : ‖absState z‖ = ‖z‖ := by
  simp only [absState,Prod.norm_def,absVector_norm]

@[simp] theorem absState_cone {M : ℝ} (z : State ι) : Cone M (absState z) ↔ Cone M z := by
  simp [Cone,absState]

@[simp] theorem absState_zero : absState (0 : State ι) = 0 := by
  ext i <;> simp [absState,absVector]

@[simp] theorem vectorAlpha_abs (lam w u : ι → ℝ) :
    vectorAlpha lam w (absVector u) = vectorAlpha lam w u := by
  simp only [vectorAlpha,quadraticForm,absVector,sq_abs]

/-- Spectral quotients depend only on coordinate magnitudes. -/
theorem vectorAlpha_congr_abs (lam w : ι → ℝ) {u v : ι → ℝ}
    (h : absVector u = absVector v) : vectorAlpha lam w u = vectorAlpha lam w v := by
  rw [← vectorAlpha_abs lam w u,← vectorAlpha_abs lam w v,h]

/-- Taking componentwise absolute values is nonexpansive in the sup norm. -/
theorem absVector_nonexpansive (u v : ι → ℝ) :
    ‖absVector u - absVector v‖ ≤ ‖u-v‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  change abs (abs (u i) - abs (v i)) ≤ ‖u-v‖
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (by simpa using norm_le_pi_norm (u-v) i)

theorem absState_nonexpansive (z z' : State ι) :
    ‖absState z - absState z'‖ ≤ ‖z-z'‖ := by
  apply norm_prod_le_iff.mpr
  exact ⟨(absVector_nonexpansive _ _).trans (norm_fst_le (z-z')),
    (absVector_nonexpansive _ _).trans (norm_snd_le (z-z'))⟩

theorem absVector_smul (u : ι → ℝ) (t : ℝ) :
    absVector (t • u) = |t| • absVector u := by
  funext i
  exact abs_mul t (u i)

theorem absState_smul (z : State ι) (t : ℝ) :
    absState (t • z) = |t| • absState z := by
  exact Prod.ext (absVector_smul _ _) (absVector_smul _ _)

/-- A state update preserves equality of coordinate magnitudes. -/
theorem stateMap_congr_abs (lam w : ι → ℝ) {z z' : State ι}
    (h : absState z = absState z') :
    absState (stateMap lam w z) = absState (stateMap lam w z') := by
  have hu : absVector z.1 = absVector z'.1 := congrArg Prod.fst h
  have hv : absVector z.2 = absVector z'.2 := congrArg Prod.snd h
  have hα := vectorAlpha_congr_abs lam w hu
  apply Prod.ext
  · exact hv
  · funext i
    change |(1-vectorAlpha lam w z.1*lam i)*z.2 i| =
      |(1-vectorAlpha lam w z'.1*lam i)*z'.2 i|
    rw [abs_mul,abs_mul,hα]
    exact congrArg (fun r => |1-vectorAlpha lam w z'.1*lam i| * r) (congrFun hv i)

/-- Scaling each update does not change sign invariance. -/
theorem scaled_stateMap_congr_abs (lam w : ι → ℝ) (t : ℝ) {z z' : State ι}
    (h : absState z = absState z') :
    absState (t • stateMap lam w z) = absState (t • stateMap lam w z') := by
  rw [absState_smul,absState_smul,stateMap_congr_abs lam w h]

variable {W : Type*}

/-- Word-level sign invariance for any family preserving component magnitudes. -/
theorem run_congr_abs {S : W → State ι → State ι}
    (hS : ∀ w z z', absState z = absState z' → absState (S w z) = absState (S w z'))
    (l : List W) {z z' : State ι} (h : absState z = absState z') :
    absState (BB.Gluing.run S l z) = absState (BB.Gluing.run S l z') := by
  induction l generalizing z z' with
  | nil => exact h
  | cons w l ih => exact ih (hS w z z' h)

theorem run_norm_congr_abs {S : W → State ι → State ι}
    (hS : ∀ w z z', absState z = absState z' → absState (S w z) = absState (S w z'))
    (l : List W) {z z' : State ι} (h : absState z = absState z') :
    ‖BB.Gluing.run S l z‖ = ‖BB.Gluing.run S l z'‖ := by
  simpa only [absState_norm] using congrArg norm (run_congr_abs hS l h)

/-- The exact norm equality needed for the block-magnitude lift. -/
theorem scaled_run_norm_abs (lam : ι → ℝ) (weights : W → ι → ℝ) (t : ℝ)
    (l : List W) (z : State ι) :
    ‖BB.Gluing.run (fun w z => t • stateMap lam (weights w) z) l (absState z)‖ =
    ‖BB.Gluing.run (fun w z => t • stateMap lam (weights w) z) l z‖ := by
  apply run_norm_congr_abs (fun w x y h => scaled_stateMap_congr_abs lam (weights w) t h) l
  exact absState_idempotent z

/-- Finite-horizon supremum is unchanged by taking coordinate magnitudes. -/
theorem horizon_abs (lam : ι → ℝ) (weights : W → ι → ℝ) (t : ℝ)
    (N : ℕ) (z : State ι) :
    BB.Gluing.horizon (fun w z => t • stateMap lam (weights w) z) N (absState z) =
    BB.Gluing.horizon (fun w z => t • stateMap lam (weights w) z) N z := by
  unfold BB.Gluing.horizon
  congr 1
  ext r
  constructor
  · rintro ⟨l,hl,hr⟩
    exact ⟨l,hl,hr.trans (scaled_run_norm_abs lam weights t l z)⟩
  · rintro ⟨l,hl,hr⟩
    exact ⟨l,hl,hr.trans (scaled_run_norm_abs lam weights t l z).symm⟩

/-- Sign invariance of the complete finite-horizon Lyapunov formula. -/
theorem finite_horizon_V_abs (lam : ι → ℝ) (weights : W → ι → ℝ) (t A : ℝ)
    (N : ℕ) (P : State ι → ℝ) (hP : ∀ z, P (absState z) = P z) (z : State ι) :
    BB.Gluing.V (fun w z => t • stateMap lam (weights w) z) N A P (absState z) =
    BB.Gluing.V (fun w z => t • stateMap lam (weights w) z) N A P z := by
  unfold BB.Gluing.V BB.Gluing.Q
  rw [absState_norm,hP,horizon_abs]

/-- The actual endpoint product is sign invariant. -/
@[simp] theorem endpointProduct_abs {n : ℕ} (lam : Fin n → ℝ)
    (lo hi : Fin n) (z : State (Fin n)) :
    BB.Faces.endpointProduct lam lo hi (absState z) = BB.Faces.endpointProduct lam lo hi z := by
  simp [BB.Faces.endpointProduct,absState,absVector]

/-- The manuscript's concrete endpoint-product Lyapunov formula is sign invariant. -/
theorem endpoint_V_abs {n : ℕ} (lam : Fin n → ℝ) (weights : W → Fin n → ℝ)
    (lo hi : Fin n) (t A : ℝ) (N : ℕ) (z : State (Fin n)) :
    BB.Gluing.V (fun w z => t • stateMap lam (weights w) z) N A
      (BB.Faces.endpointProduct lam lo hi) (absState z) =
    BB.Gluing.V (fun w z => t • stateMap lam (weights w) z) N A
      (BB.Faces.endpointProduct lam lo hi) z :=
  finite_horizon_V_abs lam weights t A N _ (endpointProduct_abs lam lo hi) z

end BB.Spectral
