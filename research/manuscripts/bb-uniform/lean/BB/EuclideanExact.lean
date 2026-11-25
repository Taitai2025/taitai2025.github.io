import BB.EuclideanRecursion

/-! # Exact recursive constants and candidate in the original operator variables

The product norm in every displayed estimate is precisely
`sqrt (‖u‖²+‖v‖²)`.  The prefactor is the literal recursive K, and the value
is the literal finite-horizon maximum.  Neither is replaced by a norm-
equivalence multiple or by an existential alternate constant.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean.System
open BB.Operator BB.Gluing

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (s : System E Ω)

def exactRate : ℝ := s.faceRate 0 (Fin.last (s.n+1))
def exactLength : ℕ := s.faceLength 0 (Fin.last (s.n+1))
def exactPrefactor : ℝ := s.facePrefactor 0 (Fin.last (s.n+1))
def exactValue (z : E × E) : ℝ := s.candidate 0 (Fin.last (s.n+1)) (ofPair z)

def rawStep (w : Ω) : E × E → E × E := stateMap s.H (s.W w)
def rawScaled (r : ℝ) (w : Ω) (z : E × E) : E × E := r⁻¹ • s.rawStep w z

theorem full_indices_lt : (0 : Fin (s.n+2))<Fin.last (s.n+1) := by
  change 0<s.n+1
  omega

theorem exactRate_pos : 0<s.exactRate := s.faceRate_pos s.full_indices_lt
theorem exactRate_lt_one : s.exactRate<1 := s.faceRate_lt_one s.full_indices_lt
theorem exactLength_ge_three : 3≤s.exactLength := s.faceLength_ge_three s.full_indices_lt
theorem exactPrefactor_ge_one : 1≤s.exactPrefactor := s.facePrefactor_ge_one s.full_indices_lt

/-- Equation `K_recursive`, with no change of norm or constants. -/
theorem exactPrefactor_formula : s.exactPrefactor=2*(s.L/s.exactRate)^s.exactLength :=
  s.facePrefactor_eq s.full_indices_lt

/-- The explicit recursive coefficient depends only on the ordered distinct
spectrum and the displayed global B,L (hence only on spectrum, χ and M). -/
theorem exactPrefactor_spectral_formula :
    s.exactPrefactor=BB.Recursive.prefactor (BB.Recursive.extend s.lam)
      (Real.sqrt (1+(s.upper/s.lower-1)^2))
      (s.upper/s.lower+2*(s.upper/s.lower)*(s.upper/s.lower-1)*s.M*Real.sqrt s.chi)
      0 (s.n+1) := by
  rfl

theorem full_domain_iff (z : Pair E) :
    z ∈ s.domain 0 (Fin.last (s.n+1)) ↔ cone s.M z := by
  constructor
  · intro hz; exact hz.1
  · intro hz
    refine ⟨hz,?_,?_⟩
    all_goals
      intro i hi
      rcases hi with hi | hi
      · exact False.elim (not_lt_of_ge (Fin.zero_le i) hi)
      · exact False.elim (not_lt_of_ge (Fin.le_last i) hi)

theorem run_scaled_ofPair (r : ℝ) (l : List Ω) (z : E × E) :
    run (s.scaled r) l (ofPair z)=ofPair (run (s.rawScaled r) l z) := by
  induction l generalizing z with
  | nil => rfl
  | cons w l ih =>
    change run (s.scaled r) l (ofPair (s.rawScaled r w z))=_
    exact ih (s.rawScaled r w z)

/-- Equation `V_construct` displayed directly in the original operator
variables.  The zero-length word is harmless because Q already dominates
the norm; positive lengths below N are precisely the manuscript's horizon. -/
theorem exactValue_formula (z : E × E) :
    s.exactValue z = max
      (max (pairNorm z)
        (s.exactPrefactor*actualEndpointProduct s.symmetric
          (spectralIndex s.H s.card 0) (spectralIndex s.H s.card (Fin.last (s.n+1))) z))
      (sSup {r : ℝ | ∃ l : List Ω, l.length<s.exactLength ∧
        r=pairNorm (run (s.rawScaled s.exactRate) l z)}) := by
  unfold exactValue candidate V BB.Gluing.Q horizon horizonValues
  rw [norm_eq_pairNorm]
  simp only [toPair_ofPair]
  change max (max (pairNorm z) (s.exactPrefactor*P s.symmetric s.card 0 (Fin.last (s.n+1)) (ofPair z)))
    (sSup {r : ℝ | ∃ l : List Ω, l.length<s.exactLength ∧ r=‖run (s.scaled s.exactRate) l (ofPair z)‖})=_
  rw [P_eq_actualEndpointProduct]
  simp only [toPair_ofPair,s.run_scaled_ofPair,norm_eq_pairNorm]

/-- The zero-length word in the total horizon definition is redundant.
Consequently this is exactly the manuscript's range `1≤j≤N−1`. -/
theorem candidate_positive_horizon [Nonempty Ω] {lo hi : Fin (s.n+2)}
    (hlohi : lo<hi) {z : Pair E} (hz : z ∈ s.domain lo hi) :
    s.candidate lo hi z = max
      (max ‖z‖ (s.facePrefactor lo hi*s.endpoint lo hi z))
      (sSup {r : ℝ | ∃ l : List Ω, 0<l.length ∧ l.length<s.faceLength lo hi ∧
        r=‖run (s.scaled (s.faceRate lo hi)) l z‖}) := by
  let S := s.scaled (s.faceRate lo hi)
  let N := s.faceLength lo hi
  let A := s.facePrefactor lo hi
  let P := s.endpoint lo hi
  let Hplus : Set ℝ := {r | ∃ l : List Ω, 0<l.length ∧ l.length<N ∧ r=‖run S l z‖}
  have hN : 1<N := by have hn := s.faceLength_ge_three hlohi; dsimp [N]; omega
  have hc := s.faceRate_pos hlohi
  have hΛ : 1≤s.L/s.faceRate lo hi :=
    (one_le_div hc).mpr ((s.faceRate_lt_one hlohi).le.trans s.L_ge_one)
  have hb : BddAbove (horizonValues S N z) :=
    horizonValues_bdd hΛ
      (fun w z hz => s.scaled_mem (s.faceRate lo hi) w hz)
      (fun w z hz => s.scaled_bound hc w hz.1) hz
  have hpos : Hplus.Nonempty := by
    let w : Ω := Classical.choice inferInstance
    exact ⟨‖run S [w] z‖,[w],by simp,by simpa using hN,rfl⟩
  have hsubset : Hplus ⊆ horizonValues S N z := by
    rintro r ⟨l,_,hl,hr⟩
    exact ⟨l,hl,hr⟩
  have hbpos : BddAbove Hplus := hb.mono hsubset
  have hposle : sSup Hplus≤horizon S N z := by
    apply csSup_le hpos
    rintro r ⟨l,_,hl,rfl⟩
    exact run_le_horizon hb l hl
  have hfullle : horizon S N z≤max (BB.Gluing.Q A P z) (sSup Hplus) := by
    apply horizon_le (by omega)
    intro l hl
    by_cases hlen : l.length=0
    · have he : l=[] := List.length_eq_zero.mp hlen
      rw [he,run_nil]
      exact (le_max_left _ _).trans (le_max_left _ _)
    · exact (le_csSup hbpos ⟨l,Nat.pos_of_ne_zero hlen,hl,rfl⟩).trans (le_max_right _ _)
  apply le_antisymm
  · exact max_le (le_max_left _ _) hfullle
  · exact max_le (le_max_left _ _) (hposle.trans (le_max_right _ _))

/-- Literal `V_construct` with precisely the positive word lengths below N,
in the original Euclidean operator variables. -/
theorem exactValue_positive_formula [Nonempty Ω] (z : E × E)
    (hz : stateCone s.M z) :
    s.exactValue z = max
      (max (pairNorm z)
        (s.exactPrefactor*actualEndpointProduct s.symmetric
          (spectralIndex s.H s.card 0) (spectralIndex s.H s.card (Fin.last (s.n+1))) z))
      (sSup {r : ℝ | ∃ l : List Ω, 0<l.length ∧ l.length<s.exactLength ∧
        r=pairNorm (run (s.rawScaled s.exactRate) l z)}) := by
  rw [exactValue,s.candidate_positive_horizon s.full_indices_lt
    ((s.full_domain_iff (ofPair z)).mpr hz)]
  rw [norm_eq_pairNorm]
  simp only [toPair_ofPair,endpoint,P_eq_actualEndpointProduct,
    s.run_scaled_ofPair,norm_eq_pairNorm]
  rfl

/-- The full-cone certificate for the literal recursive Euclidean candidate.
Only the actual SPD operator and admissible-weight assumptions in `System`
are inputs. -/
theorem exact_euclidean_certificate :
    ∃ v : EuclideanCertificate s.rawStep s.M s.exactRate s.exactPrefactor,
      v.value=s.exactValue := by
  obtain ⟨v⟩ := s.literal_interval_certificate 0 (Fin.last (s.n+1)) s.full_indices_lt
  have hzmem : ∀ z : E × E, stateCone s.M z → ofPair z ∈ s.domain 0 (Fin.last (s.n+1)) :=
    fun z hz => (s.full_domain_iff (ofPair z)).mpr hz
  refine ⟨{
    value := fun z => v.val.value (ofPair z)
    lipConstant := v.val.lipConstant
    prefactor_ge_one := s.exactPrefactor_ge_one
    lipConstant_nonneg := v.val.lipConstant_nonneg
    lower := ?_
    upper := ?_
    lipschitz := ?_
    homogeneous := ?_
    decrease := ?_
  },?_⟩
  · intro z hz
    simpa only [norm_eq_pairNorm,toPair_ofPair] using v.val.lower (ofPair z) (hzmem z hz)
  · intro z hz
    have hu := v.val.upper (ofPair z) (hzmem z hz)
    rw [v.property.2,norm_eq_pairNorm,toPair_ofPair] at hu
    exact hu
  · intro z y hz hy
    simpa only [← ofPair_sub,norm_eq_pairNorm,toPair_ofPair] using
      v.val.lipschitz (ofPair z) (ofPair y) (hzmem z hz) (hzmem y hy)
  · intro z hz t ht
    exact v.val.homogeneous (ofPair z) (hzmem z hz) t ht
  · intro w z hz
    exact v.val.decrease w (ofPair z) (hzmem z hz)
  · funext z
    exact congrFun v.property.1 (ofPair z)

/-- The original literal recursive K controls every actual trajectory from
its initial Euclidean cone membership alone. -/
theorem exact_uniform_rate (w : ℕ → Ω) (z : ℕ → E × E)
    (hz0 : stateCone s.M (z 0)) (hrec : ∀ k, z (k+1)=s.rawStep (w k) (z k)) (k : ℕ) :
    pairNorm (z k)≤s.exactPrefactor*s.exactRate^k*pairNorm (z 0) := by
  have hz : ∀ j, stateCone s.M (z j) := by
    intro j
    induction j with
    | zero => exact hz0
    | succ j ih =>
      rw [hrec j]
      exact s.step_cone (w j) (z := ofPair (z j)) ih
  obtain ⟨v,_⟩ := s.exact_euclidean_certificate
  exact v.trajectory_bound s.exactRate_pos.le w z hz hrec k

end BB.Euclidean.System
