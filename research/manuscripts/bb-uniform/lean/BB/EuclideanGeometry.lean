import BB.EuclideanPair
import BB.EuclideanProjection
import BB.OperatorSingleton
import BB.Regularization

/-! # Exact Euclidean spectral-face geometry

This file proves the actual orthogonal deletion, boundary handoff and maximum
regularization used by the literal recursive Lyapunov construction.  Neither
norm equivalence nor any assumed convergence estimate enters these results.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean
open Module.End
open BB.Operator
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
  (hn : Fintype.card (Eigenvalues H)=n)

theorem supported_iff_intervalSupported {lo hi : Fin n} {u : E} :
    supported hH hn lo hi u ↔ intervalSupported hH
      (spectralIndex H hn lo) (spectralIndex H hn hi) u := by
  constructor
  · intro hs mu hmu
    obtain ⟨i,rfl⟩ := (spectralIndex H hn).surjective mu
    apply hs i
    change sortedLambda H hn i < sortedLambda H hn lo ∨
      sortedLambda H hn hi < sortedLambda H hn i at hmu
    simpa only [(sortedLambda_strictMono H hn).lt_iff_lt] using hmu
  · intro hs i hout
    apply hs (spectralIndex H hn i)
    change sortedLambda H hn i < sortedLambda H hn lo ∨
      sortedLambda H hn hi < sortedLambda H hn i
    rcases hout with hout | hout
    · exact Or.inl ((sortedLambda_strictMono H hn) hout)
    · exact Or.inr ((sortedLambda_strictMono H hn) hout)

theorem supported_zero (lo hi : Fin n) : supported hH hn lo hi (0 : E) := by
  intro i _
  simp [sortedCoordinates,coordinates]

theorem zero_mem (M : ℝ) (lo hi : Fin n) : (0 : Pair E) ∈ stateSet hH hn M lo hi := by
  exact ⟨by simp [cone,stateCone],supported_zero hH hn lo hi,supported_zero hH hn lo hi⟩

theorem supported_smul {lo hi : Fin n} {u : E} (hu : supported hH hn lo hi u) (t : ℝ) :
    supported hH hn lo hi (t • u) := by
  intro i hi
  rw [sortedCoordinates_smul]
  change t • sortedCoordinates hH hn u i=0
  rw [hu i hi,smul_zero]

theorem stateSet_smul {M : ℝ} {lo hi : Fin n} {z : Pair E}
    (hz : z ∈ stateSet hH hn M lo hi) (t : ℝ) : t • z ∈ stateSet hH hn M lo hi := by
  refine ⟨?_,supported_smul hH hn hz.2.1 t,supported_smul hH hn hz.2.2 t⟩
  change ‖t • z.snd‖≤M*‖t • z.fst‖
  rw [norm_smul,norm_smul]
  have hh := mul_le_mul_of_nonneg_left hz.1 (norm_nonneg t)
  change ‖t‖*‖z.snd‖≤‖t‖*(M*‖z.fst‖) at hh
  nlinarith only [hh]

theorem supported_mono {lo hi lo' hi' : Fin n} {u : E}
    (hlo : lo≤lo') (hhi : hi'≤hi) (hu : supported hH hn lo' hi' u) :
    supported hH hn lo hi u := by
  intro i hi
  apply hu i
  exact hi.imp (fun h => h.trans_le hlo) (fun h => hhi.trans_lt h)

theorem stateSet_mono {M : ℝ} {lo hi lo' hi' : Fin n}
    (hlo : lo≤lo') (hhi : hi'≤hi) :
    stateSet hH hn M lo' hi' ⊆ stateSet hH hn M lo hi := by
  intro z hz
  exact ⟨hz.1,supported_mono hH hn hlo hhi hz.2.1,supported_mono hH hn hlo hhi hz.2.2⟩

theorem sortedCoordinates_step (alpha : ℝ) (v : E) (i : Fin n) :
    sortedCoordinates hH hn (v-alpha • H v) i=
      (1-alpha*sortedLambda H hn i) • sortedCoordinates hH hn v i :=
  coordinates_step hH alpha v (spectralIndex H hn i)

theorem T_supported {W : E →ₗ[ℝ] E} {lo hi : Fin n} {z : Pair E}
    (hv : supported hH hn lo hi z.snd) :
    supported hH hn lo hi (T H W z).fst ∧ supported hH hn lo hi (T H W z).snd := by
  refine ⟨hv,?_⟩
  intro i hi
  change sortedCoordinates hH hn (z.snd-weightedAlpha H W z.fst • H z.snd) i=0
  rw [sortedCoordinates_step,hv i hi,smul_zero]

theorem T_mem_of_cone {W : E →ₗ[ℝ] E} {M : ℝ} {lo hi : Fin n} {z : Pair E}
    (hz : z ∈ stateSet hH hn M lo hi) (hc : cone M (T H W z)) :
    T H W z ∈ stateSet hH hn M lo hi := ⟨hc,T_supported hH hn hz.2.2⟩

theorem P_nonnegative (lo hi : Fin n) (z : Pair E) : 0≤P hH hn lo hi z :=
  BB.geometricProduct_nonneg (norm_nonneg _) (norm_nonneg _)

theorem coordinate_pair_norm_le (i : Fin n) (z : Pair E) :
    ‖sortedCoordinates hH hn z.snd i‖≤‖z‖ :=
  (coordinate_norm_le hH hn z.snd i).trans (norm_snd_le z)

theorem P_le_norm {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    (z : Pair E) : P hH hn lo hi z≤‖z‖ :=
  BB.geometricProduct_le (BB.endpointTheta_pos ha ((sortedLambda_strictMono H hn) hlohi)).le
    (BB.endpointTheta_lt_one ha ((sortedLambda_strictMono H hn) hlohi)).le
    (norm_nonneg _) (norm_nonneg _) (coordinate_pair_norm_le hH hn lo z)
    (coordinate_pair_norm_le hH hn hi z)

theorem P_eq_zero_iff {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    (z : Pair E) : P hH hn lo hi z=0 ↔
      sortedCoordinates hH hn z.snd lo=0 ∨ sortedCoordinates hH hn z.snd hi=0 := by
  unfold P
  rw [BB.geometricProduct_eq_zero_iff (BB.endpointTheta_pos ha ((sortedLambda_strictMono H hn) hlohi))
    (BB.endpointTheta_lt_one ha ((sortedLambda_strictMono H hn) hlohi)) (norm_nonneg _) (norm_nonneg _)]
  simp only [norm_eq_zero]

theorem P_zero {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi) :
    P hH hn lo hi (0 : Pair E)=0 := by
  apply (P_eq_zero_iff hH hn ha hlohi 0).mpr
  left
  simp [sortedCoordinates,coordinates]

theorem P_homogeneous {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    (z : Pair E) {t : ℝ} (ht : 0≤t) : P hH hn lo hi (t • z)=t*P hH hn lo hi z := by
  unfold P
  rw [WithLp.smul_snd,sortedCoordinates_smul]
  simp only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg ht]
  exact BB.geometricProduct_homogeneous
    (BB.endpointTheta_pos ha ((sortedLambda_strictMono H hn) hlohi)).le
    (BB.endpointTheta_lt_one ha ((sortedLambda_strictMono H hn) hlohi)).le
    ht (norm_nonneg _) (norm_nonneg _)

theorem P_step {W : E →ₗ[ℝ] E} (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x≠0 → 0<@inner ℝ _ _ x (W x))
    {M : ℝ} {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    {z : Pair E} (hz : z ∈ stateSet hH hn M lo hi) :
    P hH hn lo hi (T H W z)≤BB.endpointRate (sortedLambda H hn lo) (sortedLambda H hn hi)*P hH hn lo hi z :=
  actualEndpointProduct_step hH hcomm hW ha ((sortedLambda_strictMono H hn) hlohi)
    hz.1 ((supported_iff_intervalSupported hH hn).mp hz.2.1)

/-- Delete only the current gradient's chosen orthogonal spectral component. -/
def eraseState (z : Pair E) (i : Fin n) : Pair E := ofPair (z.fst,erase hH hn z.snd i)

@[simp] theorem eraseState_fst (z : Pair E) (i : Fin n) : (eraseState hH hn z i).fst=z.fst := rfl
@[simp] theorem eraseState_snd (z : Pair E) (i : Fin n) :
    (eraseState hH hn z i).snd=erase hH hn z.snd i := rfl

theorem eraseState_norm_le (z : Pair E) (i : Fin n) : ‖eraseState hH hn z i‖≤‖z‖ := by
  have hsq := norm_sq (eraseState hH hn z i)
  have hsqz := norm_sq z
  have he := erase_norm_le hH hn z.snd i
  simp only [eraseState_fst,eraseState_snd] at hsq
  nlinarith only [hsq,hsqz,he,norm_nonneg (erase hH hn z.snd i),norm_nonneg z.snd,
    norm_nonneg (eraseState hH hn z i),norm_nonneg z]

theorem norm_sub_eraseState (z : Pair E) (i : Fin n) :
    ‖z-eraseState hH hn z i‖=‖sortedCoordinates hH hn z.snd i‖ := by
  have hs := norm_sq (z-eraseState hH hn z i)
  simp only [WithLp.sub_fst,WithLp.sub_snd,eraseState_fst,eraseState_snd,sub_self,norm_zero,
    zero_pow (by decide : 2≠0),zero_add,norm_sub_erase] at hs
  nlinarith only [hs,norm_nonneg (z-eraseState hH hn z i),norm_nonneg (sortedCoordinates hH hn z.snd i)]

theorem erase_supported {lo hi : Fin n} {u : E} (hu : supported hH hn lo hi u) (e : Fin n) :
    supported hH hn lo hi (erase hH hn u e) := by
  intro i hi
  by_cases hie : i=e
  · subst i
    exact erase_self hH hn u e
  · rw [erase_other hH hn u hie]
    exact hu i hi

theorem eraseState_mem {M : ℝ} {lo hi : Fin n} {z : Pair E}
    (hz : z ∈ stateSet hH hn M lo hi) (e : Fin n) :
    eraseState hH hn z e ∈ stateSet hH hn M lo hi :=
  ⟨(erase_norm_le hH hn z.snd e).trans hz.1,hz.2.1,erase_supported hH hn hz.2.2 e⟩

/-- Exact deletion-distance bound, with both the original cone and Euclidean
pair norm preserved.  The predecessor is unchanged. -/
theorem endpoint_deletion {M : ℝ} {lo hi : Fin n}
    (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi) {z : Pair E}
    (hz : z ∈ stateSet hH hn M lo hi) :
    ∃ z' ∈ stateSet hH hn M lo hi, z'.fst=z.fst ∧ P hH hn lo hi z'=0 ∧
      ‖z'‖≤‖z‖ ∧ ‖z-z'‖≤P hH hn lo hi z := by
  have hp := BB.min_le_geometricProduct
    (BB.endpointTheta_pos ha ((sortedLambda_strictMono H hn) hlohi)).le
    (BB.endpointTheta_lt_one ha ((sortedLambda_strictMono H hn) hlohi)).le
    (norm_nonneg (sortedCoordinates hH hn z.snd lo))
    (norm_nonneg (sortedCoordinates hH hn z.snd hi))
  by_cases h : ‖sortedCoordinates hH hn z.snd lo‖≤‖sortedCoordinates hH hn z.snd hi‖
  · refine ⟨eraseState hH hn z lo,eraseState_mem hH hn hz lo,rfl,?_,eraseState_norm_le hH hn z lo,?_⟩
    · exact (P_eq_zero_iff hH hn ha hlohi _).mpr (Or.inl (erase_self hH hn z.snd lo))
    · rw [norm_sub_eraseState]
      simpa only [min_eq_left h] using hp
  · refine ⟨eraseState hH hn z hi,eraseState_mem hH hn hz hi,rfl,?_,eraseState_norm_le hH hn z hi,?_⟩
    · exact (P_eq_zero_iff hH hn ha hlohi _).mpr (Or.inr (erase_self hH hn z.snd hi))
    · rw [norm_sub_eraseState]
      simpa only [min_eq_right (le_of_not_ge h)] using hp

theorem coordinate_norm_lipschitz (i : Fin n) :
    LipschitzWith 1 (fun z : Pair E => ‖sortedCoordinates hH hn z.snd i‖) := by
  apply LipschitzWith.of_dist_le_mul
  intro z z'
  simp only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm]
  calc
    |‖sortedCoordinates hH hn z.snd i‖-‖sortedCoordinates hH hn z'.snd i‖| ≤
      ‖sortedCoordinates hH hn z.snd i-sortedCoordinates hH hn z'.snd i‖ := abs_norm_sub_norm_le _ _
    _ = ‖sortedCoordinates hH hn (z.snd-z'.snd) i‖ := by rw [sortedCoordinates_sub]; rfl
    _ ≤ ‖z.snd-z'.snd‖ := coordinate_norm_le hH hn _ i
    _ ≤ ‖z-z'‖ := norm_snd_le (z-z')

theorem Q_regular {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    {A : ℝ} (hA : 1≤A) :
    ∃ J : ℝ, 0≤J ∧ ∀ x y : Pair E, |Q hH hn lo hi A x-Q hH hn lo hi A y|≤J*‖x-y‖ := by
  have hr : LipschitzWith 1 (fun z : Pair E => ‖z‖) := by
    apply LipschitzWith.of_dist_le_mul
    intro z z'
    simpa only [NNReal.coe_one,one_mul,Real.dist_eq,dist_eq_norm] using abs_norm_sub_norm_le z z'
  obtain ⟨J,hJ⟩ := BB.maximum_regularization_lipschitz
    (fun z : Pair E => ‖z‖)
    (fun z => ‖sortedCoordinates hH hn z.snd lo‖)
    (fun z => ‖sortedCoordinates hH hn z.snd hi‖)
    hA (BB.endpointTheta_pos ha ((sortedLambda_strictMono H hn) hlohi))
    (BB.endpointTheta_lt_one ha ((sortedLambda_strictMono H hn) hlohi))
    hr (coordinate_norm_lipschitz hH hn lo) (coordinate_norm_lipschitz hH hn hi)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    (coordinate_pair_norm_le hH hn lo) (coordinate_pair_norm_le hH hn hi)
  refine ⟨(J : ℝ),J.coe_nonneg,?_⟩
  intro x y
  simpa only [Q,P,Real.dist_eq,dist_eq_norm] using hJ.dist_le_mul x y

theorem Q_homogeneous {lo hi : Fin n} (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    (A : ℝ) (z : Pair E) {t : ℝ} (ht : 0≤t) : Q hH hn lo hi A (t • z)=t*Q hH hn lo hi A z := by
  unfold Q
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg ht,P_homogeneous hH hn ha hlohi z ht]
  rw [mul_left_comm A t,mul_max_of_nonneg _ _ ht]

/-- Raising the lower endpoint removes precisely its vanished projection. -/
theorem supported_raise_lower {lo hi lo' : Fin n} {u : E}
    (hnext : lo'.val=lo.val+1) (hs : supported hH hn lo hi u)
    (hzero : sortedCoordinates hH hn u lo=0) : supported hH hn lo' hi u := by
  intro i hi'
  rcases hi' with hi' | hi'
  · by_cases hieq : i=lo
    · subst i
      exact hzero
    · apply hs i
      left
      have hne : i.val≠lo.val := fun h => hieq (Fin.ext h)
      change i.val<lo.val
      change i.val<lo'.val at hi'
      omega
  · exact hs i (Or.inr hi')

theorem supported_lower_upper {lo hi hi' : Fin n} {u : E}
    (hprev : hi'.val+1=hi.val) (hs : supported hH hn lo hi u)
    (hzero : sortedCoordinates hH hn u hi=0) : supported hH hn lo hi' u := by
  intro i hi''
  rcases hi'' with hi'' | hi''
  · exact hs i (Or.inl hi'')
  · by_cases hieq : i=hi
    · subst i
      exact hzero
    · apply hs i
      right
      have hne : i.val≠hi.val := fun h => hieq (Fin.ext h)
      change hi.val<i.val
      change hi'.val<i.val at hi''
      omega

theorem T_component_zero {W : E →ₗ[ℝ] E} (z : Pair E) (i : Fin n)
    (hz : sortedCoordinates hH hn z.snd i=0) :
    sortedCoordinates hH hn (T H W z).fst i=0 ∧
      sortedCoordinates hH hn (T H W z).snd i=0 := by
  refine ⟨hz,?_⟩
  change sortedCoordinates hH hn (z.snd-weightedAlpha H W z.fst • H z.snd) i=0
  rw [sortedCoordinates_step,hz,smul_zero]

theorem T_handoff_lower {W : E →ₗ[ℝ] E} {M : ℝ} {lo hi lo' : Fin n}
    (hnext : lo'.val=lo.val+1) {z : Pair E} (hz : z ∈ stateSet hH hn M lo hi)
    (hzlo : sortedCoordinates hH hn z.snd lo=0) (hc : cone M (T H W z)) :
    T H W z ∈ stateSet hH hn M lo' hi := by
  have hm := T_mem_of_cone hH hn hz hc
  have hs := T_component_zero hH hn (W := W) z lo hzlo
  exact ⟨hm.1,supported_raise_lower hH hn hnext hm.2.1 hs.1,
    supported_raise_lower hH hn hnext hm.2.2 hs.2⟩

theorem T_handoff_upper {W : E →ₗ[ℝ] E} {M : ℝ} {lo hi hi' : Fin n}
    (hprev : hi'.val+1=hi.val) {z : Pair E} (hz : z ∈ stateSet hH hn M lo hi)
    (hzhi : sortedCoordinates hH hn z.snd hi=0) (hc : cone M (T H W z)) :
    T H W z ∈ stateSet hH hn M lo hi' := by
  have hm := T_mem_of_cone hH hn hz hc
  have hs := T_component_zero hH hn (W := W) z hi hzhi
  exact ⟨hm.1,supported_lower_upper hH hn hprev hm.2.1 hs.1,
    supported_lower_upper hH hn hprev hm.2.2 hs.2⟩

theorem boundary_handoff {W : E →ₗ[ℝ] E} {M : ℝ} {lo hi lo' hi' : Fin n}
    (ha : 0<sortedLambda H hn lo) (hlohi : lo<hi)
    (hnext : lo'.val=lo.val+1) (hprev : hi'.val+1=hi.val)
    {z : Pair E} (hz : z ∈ stateSet hH hn M lo hi) (hp : P hH hn lo hi z=0)
    (hc : cone M (T H W z)) :
    T H W z ∈ stateSet hH hn M lo' hi ∪ stateSet hH hn M lo hi' := by
  rcases (P_eq_zero_iff hH hn ha hlohi z).mp hp with hp | hp
  · exact Or.inl (T_handoff_lower hH hn hnext hz hp hc)
  · exact Or.inr (T_handoff_upper hH hn hprev hz hp hc)

/-- A vector supported in one actual eigenspace is an eigenvector or zero. -/
theorem singleton_eigenvector {i : Fin n} {u : E} (hu : supported hH hn i i u) :
    H u=sortedLambda H hn i • u := by
  apply sortedCoordinates_injective hH hn
  rw [sortedCoordinates_smul]
  funext j
  change coordinates hH (H u) (spectralIndex H hn j)=
    sortedLambda H hn i • coordinates hH u (spectralIndex H hn j)
  unfold coordinates
  rw [hH.diagonalization_apply_self_apply]
  by_cases hj : j=i
  · subst j
    rfl
  · have hz := hu j (lt_or_gt_of_ne hj)
    change hH.diagonalization u (spectralIndex H hn j)=0 at hz
    rw [hz,smul_zero,smul_zero]

theorem singleton_two_updates {W W' : E →ₗ[ℝ] E} {M : ℝ} {i : Fin n}
    (ha : 0<sortedLambda H hn i)
    (hW : ∀ x : E, x≠0 → 0<@inner ℝ _ _ x (W x)) {z : Pair E}
    (hz : z ∈ stateSet hH hn M i i) : T H W' (T H W z)=0 := by
  apply (WithLp.equiv 2 (E × E)).injective
  change stateMap H W' (stateMap H W (toPair z))=0
  exact two_updates_single_eigenvalue ha hW hz.1
    (singleton_eigenvector hH hn hz.2.1) (singleton_eigenvector hH hn hz.2.2)

end BB.Euclidean
