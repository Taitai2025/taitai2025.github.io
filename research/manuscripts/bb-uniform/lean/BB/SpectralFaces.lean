import BB.ScalarStep
import BB.Endpoint
import BB.Regularization
import BB.ScalarSupport
import BB.Gluing

/-! # Invariant spectral intervals and endpoint deletion

Coordinates use the sup norm.  This is stated explicitly; no Euclidean
norm is silently identified with the sup norm.
-/

noncomputable section
namespace BB.Faces

open BB.Spectral

variable {n : ℕ}

def supported (lo hi : Fin n) (u : Fin n → ℝ) : Prop :=
  ∀ i, i < lo ∨ hi < i → u i = 0

def stateSet (M : ℝ) (lo hi : Fin n) : Set (State (Fin n)) :=
  {z | Cone M z ∧ supported lo hi z.1 ∧ supported lo hi z.2}

theorem supported_zero (lo hi : Fin n) : supported lo hi 0 := by
  intro i hi
  rfl

theorem zero_mem (M : ℝ) (lo hi : Fin n) : (0 : State (Fin n)) ∈ stateSet M lo hi := by
  exact ⟨by simp [Cone], supported_zero lo hi, supported_zero lo hi⟩

theorem supported_smul {lo hi : Fin n} {u : Fin n → ℝ}
    (hu : supported lo hi u) (t : ℝ) : supported lo hi (t • u) := by
  intro i hi
  simp [Pi.smul_apply, hu i hi]

theorem stateSet_smul {M : ℝ} {lo hi : Fin n} {z : State (Fin n)}
    (hz : z ∈ stateSet M lo hi) (t : ℝ) : t • z ∈ stateSet M lo hi := by
  refine ⟨?_, supported_smul hz.2.1 t, supported_smul hz.2.2 t⟩
  change ‖t • z.2‖ ≤ M * ‖t • z.1‖
  rw [norm_smul, norm_smul]
  have h := mul_le_mul_of_nonneg_left hz.1 (norm_nonneg t)
  nlinarith only [h]

theorem stateMap_supported {lam w : Fin n → ℝ} {lo hi : Fin n}
    {z : State (Fin n)} (hv : supported lo hi z.2) :
    supported lo hi (stateMap lam w z).1 ∧
      supported lo hi (stateMap lam w z).2 := by
  refine ⟨hv, ?_⟩
  intro i hi
  simp [stateMap, diagonalStep, hv i hi]

theorem stateMap_mem {lam w : Fin n → ℝ} {a b M : ℝ} {lo hi : Fin n}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (hM : b/a-1 ≤ M) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi) :
    stateMap lam w z ∈ stateSet M lo hi :=
  ⟨stateMap_cone ha hab hw hlama hlamb hM hz.1, stateMap_supported hz.2.2⟩

theorem supported_mono {lo hi lo' hi' : Fin n} {u : Fin n → ℝ}
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) (hu : supported lo' hi' u) :
    supported lo hi u := by
  intro i h
  apply hu i
  rcases h with h | h
  · exact Or.inl (lt_of_lt_of_le h hlo)
  · exact Or.inr (lt_of_le_of_lt hhi h)

theorem stateSet_mono {M : ℝ} {lo hi lo' hi' : Fin n}
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    stateSet M lo' hi' ⊆ stateSet M lo hi := by
  intro z hz
  exact ⟨hz.1, supported_mono hlo hhi hz.2.1, supported_mono hlo hhi hz.2.2⟩

def erase (u : Fin n → ℝ) (e : Fin n) : Fin n → ℝ := Function.update u e 0

@[simp] theorem erase_self (u : Fin n → ℝ) (e : Fin n) : erase u e e = 0 := by
  simp [erase]

theorem erase_other (u : Fin n → ℝ) {e i : Fin n} (hi : i ≠ e) : erase u e i = u i := by
  simp [erase, hi]

theorem erase_norm_le (u : Fin n → ℝ) (e : Fin n) : ‖erase u e‖ ≤ ‖u‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
  intro i
  by_cases hi : i = e
  · subst i; simp
  · rw [erase_other u hi]
    exact norm_le_pi_norm u i

theorem norm_sub_erase (u : Fin n → ℝ) (e : Fin n) : ‖u - erase u e‖ = |u e| := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
    intro i
    by_cases hi : i = e
    · subst i; simp
    · simp [Pi.sub_apply, erase_other u hi]
  · have h := norm_le_pi_norm (u - erase u e) e
    simpa using h

def eraseState (z : State (Fin n)) (e : Fin n) : State (Fin n) := (z.1, erase z.2 e)

theorem eraseState_norm_le (z : State (Fin n)) (e : Fin n) : ‖eraseState z e‖ ≤ ‖z‖ := by
  apply norm_prod_le_iff.mpr
  exact ⟨norm_fst_le z, (erase_norm_le z.2 e).trans (norm_snd_le z)⟩

theorem norm_sub_eraseState (z : State (Fin n)) (e : Fin n) :
    ‖z - eraseState z e‖ = |z.2 e| := by
  change ‖(z.1-z.1, z.2-erase z.2 e)‖ = |z.2 e|
  simp [Prod.norm_def, norm_sub_erase]

theorem erase_supported {lo hi : Fin n} {u : Fin n → ℝ}
    (hu : supported lo hi u) (e : Fin n) : supported lo hi (erase u e) := by
  intro i hi
  by_cases hie : i = e
  · subst i; simp
  · rw [erase_other u hie]
    exact hu i hi

theorem eraseState_mem {M : ℝ} {lo hi : Fin n} {z : State (Fin n)}
    (hz : z ∈ stateSet M lo hi) (e : Fin n) : eraseState z e ∈ stateSet M lo hi := by
  exact ⟨(erase_norm_le z.2 e).trans hz.1, hz.2.1, erase_supported hz.2.2 e⟩

def endpointProduct (lam : Fin n → ℝ) (lo hi : Fin n) (z : State (Fin n)) : ℝ :=
  BB.geometricProduct (BB.endpointTheta (lam lo) (lam hi)) |z.2 lo| |z.2 hi|

theorem endpointProduct_nonneg (lam : Fin n → ℝ) (lo hi : Fin n) (z : State (Fin n)) :
    0 ≤ endpointProduct lam lo hi z := BB.geometricProduct_nonneg (abs_nonneg _) (abs_nonneg _)

theorem endpointProduct_le_norm {lam : Fin n → ℝ} {lo hi : Fin n}
    (ha : 0 < lam lo) (hab : lam lo < lam hi) (z : State (Fin n)) :
    endpointProduct lam lo hi z ≤ ‖z‖ := by
  apply BB.geometricProduct_le (BB.endpointTheta_pos ha hab).le
    (BB.endpointTheta_lt_one ha hab).le (abs_nonneg _) (abs_nonneg _)
  · exact (show |z.2 lo| ≤ ‖z.2‖ by simpa using norm_le_pi_norm z.2 lo).trans (norm_snd_le z)
  · exact (show |z.2 hi| ≤ ‖z.2‖ by simpa using norm_le_pi_norm z.2 hi).trans (norm_snd_le z)

theorem endpointProduct_eq_zero_iff {lam : Fin n → ℝ} {lo hi : Fin n}
    (ha : 0 < lam lo) (hab : lam lo < lam hi) (z : State (Fin n)) :
    endpointProduct lam lo hi z = 0 ↔ z.2 lo = 0 ∨ z.2 hi = 0 := by
  unfold endpointProduct
  rw [BB.geometricProduct_eq_zero_iff (BB.endpointTheta_pos ha hab)
    (BB.endpointTheta_lt_one ha hab) (abs_nonneg _) (abs_nonneg _)]
  simp

theorem endpointProduct_homogeneous {lam : Fin n → ℝ} {lo hi : Fin n}
    (ha : 0 < lam lo) (hab : lam lo < lam hi) (z : State (Fin n)) {t : ℝ}
    (ht : 0 ≤ t) : endpointProduct lam lo hi (t • z) = t * endpointProduct lam lo hi z := by
  unfold endpointProduct
  change BB.geometricProduct _ |t * z.2 lo| |t * z.2 hi| = _
  rw [abs_mul, abs_mul, abs_of_nonneg ht]
  exact BB.geometricProduct_homogeneous (BB.endpointTheta_pos ha hab).le
    (BB.endpointTheta_lt_one ha hab).le ht (abs_nonneg _) (abs_nonneg _)

/-- Delete the smaller endpoint without increasing either the state norm or
the cone ratio; its distance is bounded by the actual endpoint product. -/
theorem endpoint_deletion {lam : Fin n → ℝ} {lo hi : Fin n} {M : ℝ}
    (ha : 0 < lam lo) (hab : lam lo < lam hi) {z : State (Fin n)}
    (hz : z ∈ stateSet M lo hi) :
    ∃ z' ∈ stateSet M lo hi, endpointProduct lam lo hi z' = 0 ∧
      ‖z'‖ ≤ ‖z‖ ∧ ‖z-z'‖ ≤ endpointProduct lam lo hi z := by
  have hp := BB.min_le_geometricProduct (BB.endpointTheta_pos ha hab).le
    (BB.endpointTheta_lt_one ha hab).le (abs_nonneg (z.2 lo)) (abs_nonneg (z.2 hi))
  by_cases h : |z.2 lo| ≤ |z.2 hi|
  · refine ⟨eraseState z lo, eraseState_mem hz lo, ?_, eraseState_norm_le z lo, ?_⟩
    · apply (endpointProduct_eq_zero_iff ha hab _).mpr
      exact Or.inl (erase_self z.2 lo)
    · rw [norm_sub_eraseState]
      simpa only [min_eq_left h] using hp
  · refine ⟨eraseState z hi, eraseState_mem hz hi, ?_, eraseState_norm_le z hi, ?_⟩
    · apply (endpointProduct_eq_zero_iff ha hab _).mpr
      exact Or.inr (erase_self z.2 hi)
    · rw [norm_sub_eraseState]
      simpa only [min_eq_right (le_of_not_ge h)] using hp

theorem quotient_bounds {lam w : Fin n → ℝ} {lo hi : Fin n}
    (hpos : 0 < lam lo) (hmono : Monotone lam) (hlohi : lo ≤ hi)
    (hw : ∀ i, 1 ≤ w i) {u : Fin n → ℝ} (hu : u ≠ 0)
    (hs : supported lo hi u) :
    1 / lam hi ≤ vectorAlpha lam w u ∧ vectorAlpha lam w u ≤ 1 / lam lo := by
  apply vectorAlpha_bounds_on_support hpos (hmono hlohi) hw ?_ hu
  intro i
  by_cases hi : i < lo ∨ hi < i
  · exact Or.inl (hs i hi)
  · right
    push_neg at hi
    exact ⟨hmono hi.1, hmono hi.2⟩

theorem endpointProduct_step {lam w : Fin n → ℝ} {lo hi : Fin n} {M : ℝ}
    (hpos : 0 < lam lo) (hmono : StrictMono lam) (hlohi : lo < hi)
    (hw : ∀ i, 1 ≤ w i) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi) :
    endpointProduct lam lo hi (stateMap lam w z) ≤
      BB.endpointRate (lam lo) (lam hi) * endpointProduct lam lo hi z := by
  by_cases hu : z.1 = 0
  · have hzero := cone_eq_zero_of_fst hz.1 hu
    subst z
    rw [stateMap_zero]
    have hpzero : endpointProduct lam lo hi (0 : State (Fin n)) = 0 :=
      (endpointProduct_eq_zero_iff hpos (hmono hlohi) _).mpr (Or.inl rfl)
    simp only [hpzero, mul_zero, le_refl]
  · obtain ⟨hlo,hhi⟩ := quotient_bounds hpos hmono.monotone hlohi.le hw hu hz.2.1
    unfold endpointProduct
    change BB.geometricProduct _ |(1 - vectorAlpha lam w z.1 * lam lo) * z.2 lo|
      |(1 - vectorAlpha lam w z.1 * lam hi) * z.2 hi| ≤ _
    rw [abs_mul, abs_mul]
    exact BB.endpointProduct_decay_stepsize hpos (hmono hlohi) hlo hhi (abs_nonneg _) (abs_nonneg _)

theorem coordinate_abs_lipschitz (i : Fin n) :
    LipschitzWith 1 (fun z : State (Fin n) => |z.2 i|) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  simp only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm]
  calc
    |(|z.2 i| - |z'.2 i|)| ≤ |z.2 i - z'.2 i| := abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ ‖z.2-z'.2‖ := by simpa using norm_le_pi_norm (z.2-z'.2) i
    _ ≤ ‖z-z'‖ := norm_snd_le (z-z')

theorem endpoint_Q_regular {lam : Fin n → ℝ} {lo hi : Fin n}
    (ha : 0 < lam lo) (hab : lam lo < lam hi) {A : ℝ} (hA : 1 ≤ A) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ x y : State (Fin n),
      |BB.Gluing.Q A (endpointProduct lam lo hi) x -
        BB.Gluing.Q A (endpointProduct lam lo hi) y| ≤ J * ‖x-y‖ := by
  have hr : LipschitzWith 1 (fun z : State (Fin n) => ‖z‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, dist_eq_norm] using abs_norm_sub_norm_le z z'
  have hlo (z : State (Fin n)) : |z.2 lo| ≤ ‖z‖ :=
    (show |z.2 lo| ≤ ‖z.2‖ by simpa using norm_le_pi_norm z.2 lo).trans (norm_snd_le z)
  have hhi (z : State (Fin n)) : |z.2 hi| ≤ ‖z‖ :=
    (show |z.2 hi| ≤ ‖z.2‖ by simpa using norm_le_pi_norm z.2 hi).trans (norm_snd_le z)
  obtain ⟨J,hJ⟩ := BB.maximum_regularization_lipschitz
    (fun z : State (Fin n) => ‖z‖) (fun z => |z.2 lo|) (fun z => |z.2 hi|)
    hA (BB.endpointTheta_pos ha hab) (BB.endpointTheta_lt_one ha hab)
    hr (coordinate_abs_lipschitz lo) (coordinate_abs_lipschitz hi)
    (fun z => abs_nonneg _) (fun z => abs_nonneg _) hlo hhi
  refine ⟨(J : ℝ), J.coe_nonneg, ?_⟩
  intro x y
  simpa only [BB.Gluing.Q, endpointProduct, Real.dist_eq, dist_eq_norm] using hJ.dist_le_mul x y

theorem supported_raise_lower {lo hi lo' : Fin n} {u : Fin n → ℝ}
    (hnext : lo'.val = lo.val + 1) (hs : supported lo hi u) (hzero : u lo = 0) :
    supported lo' hi u := by
  intro i hi'
  rcases hi' with hi' | hi'
  · by_cases hieq : i = lo
    · simpa [hieq] using hzero
    · apply hs i
      left
      have hne : i.val ≠ lo.val := fun h => hieq (Fin.ext h)
      change i.val < lo.val
      change i.val < lo'.val at hi'
      omega
  · exact hs i (Or.inr hi')

theorem supported_lower_upper {lo hi hi' : Fin n} {u : Fin n → ℝ}
    (hprev : hi'.val + 1 = hi.val) (hs : supported lo hi u) (hzero : u hi = 0) :
    supported lo hi' u := by
  intro i hi''
  rcases hi'' with hi'' | hi''
  · exact hs i (Or.inl hi'')
  · by_cases hieq : i = hi
    · simpa [hieq] using hzero
    · apply hs i
      right
      have hne : i.val ≠ hi.val := fun h => hieq (Fin.ext h)
      change hi.val < i.val
      change hi'.val < i.val at hi''
      omega

theorem stateMap_handoff_lower {lam w : Fin n → ℝ} {a b M : ℝ} {lo hi lo' : Fin n}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (hnext : lo'.val = lo.val+1) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi)
    (hzlo : z.2 lo = 0) : stateMap lam w z ∈ stateSet M lo' hi := by
  have hmem := stateMap_mem ha hab hw hlama hlamb hM hz
  have hs := stateMap_component_zero lam w z lo hzlo
  exact ⟨hmem.1, supported_raise_lower hnext hmem.2.1 hs.1,
    supported_raise_lower hnext hmem.2.2 hs.2⟩

theorem stateMap_handoff_upper {lam w : Fin n → ℝ} {a b M : ℝ} {lo hi hi' : Fin n}
    (ha : 0 < a) (hab : a ≤ b) (hw : ∀ i, 1 ≤ w i)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (hprev : hi'.val+1 = hi.val) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi)
    (hzhi : z.2 hi = 0) : stateMap lam w z ∈ stateSet M lo hi' := by
  have hmem := stateMap_mem ha hab hw hlama hlamb hM hz
  have hs := stateMap_component_zero lam w z hi hzhi
  exact ⟨hmem.1, supported_lower_upper hprev hmem.2.1 hs.1,
    supported_lower_upper hprev hmem.2.2 hs.2⟩

theorem singleton_support {i : Fin n} {u : Fin n → ℝ} (hu : supported i i u) :
    ∀ j, u j = 0 ∨ j = i := by
  intro j
  by_cases h : j = i
  · exact Or.inr h
  · left
    exact hu j (lt_or_gt_of_ne h)

theorem singleton_two_updates {lam w w' : Fin n → ℝ} {M : ℝ} {i : Fin n}
    (ha : 0 < lam i) (hw : ∀ j, 1 ≤ w j) {z : State (Fin n)}
    (hz : z ∈ stateSet M i i) : stateMap lam w' (stateMap lam w z) = 0 := by
  apply two_updates_single_eigenvalue ha hw hz.1
  · intro j
    rcases singleton_support hz.2.1 j with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg lam h)
  · intro j
    rcases singleton_support hz.2.2 j with h | h
    · exact Or.inl h
    · exact Or.inr (congrArg lam h)

/-- Moving the lower endpoint strictly improves the critical factor. -/
theorem rate_raise_lower {a a' b : ℝ} (ha : 0 < a) (haa' : a < a') (ha'b : a' ≤ b) :
    BB.endpointRate a' b < BB.endpointRate a b := by
  unfold BB.endpointRate
  apply (div_lt_div_iff (by linarith : 0 < b+a') (by linarith : 0 < b+a)).mpr
  have h := mul_pos (by linarith : 0 < b) (sub_pos.mpr haa')
  nlinarith

/-- Moving the upper endpoint strictly improves the critical factor. -/
theorem rate_lower_upper {a b' b : ℝ} (ha : 0 < a) (hab' : a ≤ b') (hb'b : b' < b) :
    BB.endpointRate a b' < BB.endpointRate a b := by
  unfold BB.endpointRate
  apply (div_lt_div_iff (by linarith : 0 < b'+a) (by linarith : 0 < b+a)).mpr
  have h := mul_pos ha (sub_pos.mpr hb'b)
  nlinarith

end BB.Faces
