import BB.OperatorBounds

set_option autoImplicit false

noncomputable section
namespace BB.Spectral
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Positive mass on both endpoint eigenspaces makes both moment bounds strict. -/
theorem denominator_strict_bounds {lam w e : ι → ℝ} {a b : ℝ} {ia ib : ι}
    (hab : a < b) (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 < w i)
    (hlo : ∀ i, a ≤ lam i) (hhi : ∀ i, lam i ≤ b)
    (hia : lam ia = a) (hib : lam ib = b) (hea : 0 < e ia) (heb : 0 < e ib) :
    0 < numerator w e ∧ a*numerator w e < denominator lam w e ∧
      denominator lam w e < b*numerator w e := by
  classical
  have hN : 0 < numerator w e := by
    apply (mul_pos (hw ia) hea).trans_le
    exact Finset.single_le_sum (fun i _ => mul_nonneg (hw i).le (he i)) (Finset.mem_univ ia)
  refine ⟨hN,?_,?_⟩
  · unfold numerator denominator
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro i _
      have hh := mul_le_mul_of_nonneg_left (hlo i) (mul_nonneg (hw i).le (he i))
      nlinarith only [hh]
    · refine ⟨ib,Finset.mem_univ ib,?_⟩
      rw [hib]
      have hh := mul_lt_mul_of_pos_left hab (mul_pos (hw ib) heb)
      nlinarith only [hh]
  · unfold numerator denominator
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum
    · intro i _
      have hh := mul_le_mul_of_nonneg_left (hhi i) (mul_nonneg (hw i).le (he i))
      nlinarith only [hh]
    · refine ⟨ia,Finset.mem_univ ia,?_⟩
      rw [hia]
      have hh := mul_lt_mul_of_pos_left hab (mul_pos (hw ia) hea)
      nlinarith only [hh]

/-- A positive weighted quotient is strictly interior whenever both extreme
spectral energies are present. -/
theorem alpha_strict_bounds {lam w e : ι → ℝ} {a b : ℝ} {ia ib : ι}
    (ha : 0 < a) (hab : a < b) (he : ∀ i, 0 ≤ e i) (hw : ∀ i, 0 < w i)
    (hlo : ∀ i, a ≤ lam i) (hhi : ∀ i, lam i ≤ b)
    (hia : lam ia = a) (hib : lam ib = b) (hea : 0 < e ia) (heb : 0 < e ib) :
    1/b < alpha lam w e ∧ alpha lam w e < 1/a := by
  obtain ⟨hN,hloD,hhiD⟩ := denominator_strict_bounds hab he hw hlo hhi hia hib hea heb
  have hD : 0 < denominator lam w e := (mul_pos ha hN).trans hloD
  unfold alpha
  constructor
  · apply (div_lt_div_iff (ha.trans hab) hD).mpr
    nlinarith only [hhiD]
  · apply (div_lt_div_iff hD ha).mpr
    nlinarith only [hloD]

theorem vectorAlpha_strict_bounds {lam w u : ι → ℝ} {a b : ℝ} {ia ib : ι}
    (ha : 0 < a) (hab : a < b) (hw : ∀ i, 0 < w i)
    (hlo : ∀ i, a ≤ lam i) (hhi : ∀ i, lam i ≤ b)
    (hia : lam ia = a) (hib : lam ib = b) (hua : u ia ≠ 0) (hub : u ib ≠ 0) :
    1/b < vectorAlpha lam w u ∧ vectorAlpha lam w u < 1/a := by
  rw [vectorAlpha_eq]
  exact alpha_strict_bounds ha hab (fun i => sq_nonneg _) hw hlo hhi hia hib
    (sq_pos_of_ne_zero hua) (sq_pos_of_ne_zero hub)

end BB.Spectral

namespace BB.Operator
open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Both actual orthogonal endpoint projections are nonzero. -/
def endpointPresent {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) (u : E) : Prop :=
  coordinates hH u lo ≠ 0 ∧ coordinates hH u hi ≠ 0

def endpointStatePresent {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) (z : E × E) : Prop :=
  endpointPresent hH lo hi z.1 ∧ endpointPresent hH lo hi z.2

theorem blockEnergy_pos {H W : E →ₗ[ℝ] E}
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    (mu : Eigenvalues H) (x : eigenspace H (mu:ℝ)) (hx : x ≠ 0) :
    0 < blockEnergy W mu x := by
  apply hW
  intro hzero
  apply hx
  exact Subtype.ext hzero

theorem blockEnergy_nonneg {H W : E →ₗ[ℝ] E}
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    (mu : Eigenvalues H) (x : eigenspace H (mu:ℝ)) : 0 ≤ blockEnergy W mu x := by
  by_cases hx : x = 0
  · simp [blockEnergy,hx]
  · exact (blockEnergy_pos hW mu x hx).le

/-- The actual positive commuting operator quotient is strictly interior when
both endpoint components of its argument are present. -/
theorem weightedAlpha_strict_bounds {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo:ℝ)) (hab : (lo:ℝ) < (hi:ℝ))
    (hspec : ∀ mu : Eigenvalues H, (lo:ℝ) ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ (hi:ℝ))
    {u : E} (hu : endpointPresent hH lo hi u) :
    1/(hi:ℝ) < weightedAlpha H W u ∧ weightedAlpha H W u < 1/(lo:ℝ) := by
  let e : Eigenvalues H → ℝ := fun mu => blockEnergy W mu (coordinates hH u mu)
  have he : ∀ mu, 0 ≤ e mu := fun mu => blockEnergy_nonneg hW mu (coordinates hH u mu)
  have hea : 0 < e lo := blockEnergy_pos hW lo (coordinates hH u lo) hu.1
  have heb : 0 < e hi := blockEnergy_pos hW hi (coordinates hH u hi) hu.2
  have halpha : weightedAlpha H W u = BB.Spectral.alpha
      (fun mu : Eigenvalues H => (mu:ℝ)) (fun _ => 1) e := by
    rw [weightedAlpha_blocks hH hcomm]
    simp only [BB.Blocks.blockAlpha,BB.Spectral.alpha,BB.Spectral.numerator,
      BB.Spectral.denominator,one_mul,e]
  rw [halpha]
  exact BB.Spectral.alpha_strict_bounds ha hab he (fun _ => by norm_num)
    (fun mu => (hspec mu).1) (fun mu => (hspec mu).2) rfl rfl hea heb

def weightedTau (H W : E →ₗ[ℝ] E) (u : E) : ℝ :=
  @inner ℝ _ _ u (W (H u)) / @inner ℝ _ _ u (W u)

theorem weightedTau_eq (H W : E →ₗ[ℝ] E) (u : E) :
    weightedTau H W u = 1/weightedAlpha H W u := by
  simp only [weightedTau,weightedAlpha,one_div_div]

/-- The reciprocal Rayleigh mean in the exact dissipation law lies in the open
endpoint interval for the actual operator quotient. -/
theorem weightedTau_strict_bounds {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo:ℝ)) (hab : (lo:ℝ) < (hi:ℝ))
    (hspec : ∀ mu : Eigenvalues H, (lo:ℝ) ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ (hi:ℝ))
    {u : E} (hu : endpointPresent hH lo hi u) :
    (lo:ℝ) < weightedTau H W u ∧ weightedTau H W u < (hi:ℝ) := by
  obtain ⟨hlo,hhi⟩ := weightedAlpha_strict_bounds hH hcomm hW ha hab hspec hu
  have hb := ha.trans hab
  have hpos : 0 < weightedAlpha H W u := (one_div_pos.mpr hb).trans hlo
  rw [weightedTau_eq]
  constructor
  · apply (lt_div_iff hpos).mpr
    have hh := (lt_div_iff ha).mp hhi
    nlinarith only [hh]
  · apply (div_lt_iff hpos).mpr
    have hh := (div_lt_iff hb).mp hlo
    nlinarith only [hh]

/-- A state with both endpoints in both entries retains them after one update. -/
theorem stateMap_endpoint_persistence {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo:ℝ)) (hab : (lo:ℝ) < (hi:ℝ))
    (hspec : ∀ mu : Eigenvalues H, (lo:ℝ) ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ (hi:ℝ))
    {z : E × E} (hz : endpointStatePresent hH lo hi z) :
    endpointStatePresent hH lo hi (stateMap H W z) := by
  obtain ⟨hlo,hhi⟩ := weightedAlpha_strict_bounds hH hcomm hW ha hab hspec hz.1
  refine ⟨hz.2,?_,?_⟩
  · change coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) lo ≠ 0
    rw [coordinates_step]
    apply smul_ne_zero _ hz.2.1
    exact ne_of_gt (sub_pos.mpr ((lt_div_iff ha).mp hhi))
  · change coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) hi ≠ 0
    rw [coordinates_step]
    apply smul_ne_zero _ hz.2.2
    exact ne_of_lt (sub_neg.mpr ((div_lt_iff (ha.trans hab)).mp hlo))

/-- Endpoint persistence along every actual changing-weight delayed trajectory.
No bound on the condition numbers is needed for this algebraic statement. -/
theorem endpoint_state_persistence {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (W : ℕ → E →ₗ[ℝ] E) (hcomm : ∀ k, Function.Commute H (W k))
    (hW : ∀ k, ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W k x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo:ℝ)) (hab : (lo:ℝ) < (hi:ℝ))
    (hspec : ∀ mu : Eigenvalues H, (lo:ℝ) ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ (hi:ℝ))
    (z : ℕ → E × E) (hz : endpointStatePresent hH lo hi (z 0))
    (hrec : ∀ k, z (k+1) = stateMap H (W k) (z k)) :
    ∀ k, endpointStatePresent hH lo hi (z k) := by
  intro k
  induction k with
  | zero => exact hz
  | succ k ih =>
    rw [hrec k]
    exact stateMap_endpoint_persistence hH (hcomm k) (hW k) ha hab hspec ih

/-- In particular, every reciprocal quotient in the tail is strictly interior,
discharging the open-interval premise of the exact endpoint-defect identity. -/
theorem trajectory_weightedTau_interior {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (W : ℕ → E →ₗ[ℝ] E) (hcomm : ∀ k, Function.Commute H (W k))
    (hW : ∀ k, ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W k x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo:ℝ)) (hab : (lo:ℝ) < (hi:ℝ))
    (hspec : ∀ mu : Eigenvalues H, (lo:ℝ) ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ (hi:ℝ))
    (z : ℕ → E × E) (hz : endpointStatePresent hH lo hi (z 0))
    (hrec : ∀ k, z (k+1) = stateMap H (W k) (z k)) (k : ℕ) :
    (lo:ℝ) < weightedTau H (W k) (z k).1 ∧ weightedTau H (W k) (z k).1 < (hi:ℝ) :=
  weightedTau_strict_bounds hH (hcomm k) (hW k) ha hab hspec
    (endpoint_state_persistence hH W hcomm hW ha hab hspec z hz hrec k).1

end BB.Operator
