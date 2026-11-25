import BB.EndpointPersistence

/-! # Actual endpoint persistence on an active spectral interval

The ambient Hessian may have eigenvalues outside the active interval.  Their
actual gradient projections vanish and remain zero.  Clamping these unused
eigenvalues leaves the actual weighted quotient unchanged, giving the strict
endpoint bounds needed by the baseline on every active face.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Operator
open Module.End
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- No actual spectral component lies outside the stated active interval. -/
def intervalSupported {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) (u : E) : Prop :=
  ∀ mu : Eigenvalues H, (mu : ℝ) < (lo : ℝ) ∨ (hi : ℝ) < (mu : ℝ) → coordinates hH u mu=0

def intervalStateSupported {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) (z : E × E) : Prop :=
  intervalSupported hH lo hi z.1 ∧ intervalSupported hH lo hi z.2

/-- Global spectral endpoints are a special case of an active interval. -/
theorem intervalSupported_of_global_bounds {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H}
    (hspec : ∀ mu : Eigenvalues H, (lo : ℝ) ≤ (mu : ℝ) ∧ (mu : ℝ) ≤ (hi : ℝ)) (u : E) :
    intervalSupported hH lo hi u := by
  intro mu hmu
  rcases hmu with hmu | hmu
  · exact ((hspec mu).1.not_lt hmu).elim
  · exact ((hspec mu).2.not_lt hmu).elim

/-- Strict true quotient bounds depend only on eigenvalues with nonzero actual
projection, and therefore hold at the endpoints of every invariant active face. -/
theorem weightedAlpha_strict_bounds_on_support {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    {u : E} (hs : intervalSupported hH lo hi u) (hu : endpointPresent hH lo hi u) :
    1/(hi : ℝ) < weightedAlpha H W u ∧ weightedAlpha H W u < 1/(lo : ℝ) := by
  let e : Eigenvalues H → ℝ := fun mu => blockEnergy W mu (coordinates hH u mu)
  let lam : Eigenvalues H → ℝ := fun mu => min (hi : ℝ) (max (lo : ℝ) (mu : ℝ))
  have he : ∀ mu, 0 ≤ e mu := fun mu => blockEnergy_nonneg hW mu (coordinates hH u mu)
  have hloa : ∀ mu, (lo : ℝ) ≤ lam mu := fun mu => le_min hab.le (le_max_left _ _)
  have hhib : ∀ mu, lam mu ≤ (hi : ℝ) := fun mu => min_le_left _ _
  have hia : lam lo=(lo : ℝ) := by simp [lam,min_eq_right hab.le]
  have hib : lam hi=(hi : ℝ) := by simp [lam,max_eq_right hab.le]
  have hden : (∑ mu : Eigenvalues H,(mu : ℝ)*e mu)=∑ mu : Eigenvalues H,lam mu*e mu := by
    apply Finset.sum_congr rfl
    intro mu _
    by_cases hout : (mu : ℝ) < (lo : ℝ) ∨ (hi : ℝ) < (mu : ℝ)
    · have hz := hs mu hout
      simp [e,blockEnergy,hz]
    · push_neg at hout
      simp only [lam,max_eq_right hout.1,min_eq_right hout.2]
  have halpha : weightedAlpha H W u=BB.Spectral.alpha lam (fun _ => 1) e := by
    rw [weightedAlpha_blocks hH hcomm]
    change (∑ mu : Eigenvalues H,e mu)/(∑ mu : Eigenvalues H,(mu : ℝ)*e mu)=_
    rw [hden]
    simp [BB.Spectral.alpha,BB.Spectral.numerator,BB.Spectral.denominator]
  rw [halpha]
  exact BB.Spectral.alpha_strict_bounds ha hab he (fun _ => by norm_num) hloa hhib hia hib
    (blockEnergy_pos hW lo _ hu.1) (blockEnergy_pos hW hi _ hu.2)

/-- The active-face reciprocal quotient is strictly interior. -/
theorem weightedTau_strict_bounds_on_support {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    {u : E} (hs : intervalSupported hH lo hi u) (hu : endpointPresent hH lo hi u) :
    (lo : ℝ) < weightedTau H W u ∧ weightedTau H W u < (hi : ℝ) := by
  obtain ⟨hlo,hhi⟩ := weightedAlpha_strict_bounds_on_support hH hcomm hW ha hab hs hu
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

/-- The operator update preserves every interval containing the active components. -/
theorem stateMap_interval_supported {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    {lo hi : Eigenvalues H} {z : E × E} (hs : intervalSupported hH lo hi z.2) :
    intervalStateSupported hH lo hi (stateMap H W z) := by
  refine ⟨hs,?_⟩
  intro mu hmu
  change coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) mu=0
  rw [coordinates_step,hs mu hmu,smul_zero]

theorem trajectory_interval_supported {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (W : ℕ → E →ₗ[ℝ] E) {lo hi : Eigenvalues H}
    (z : ℕ → E × E) (hs : intervalStateSupported hH lo hi (z 0))
    (hrec : ∀ n, z (n+1)=stateMap H (W n) (z n)) :
    ∀ n, intervalStateSupported hH lo hi (z n) := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih =>
    rw [hrec]
    exact stateMap_interval_supported hH ih.2

/-- Endpoint presence persists without assuming that these are global ambient
spectral endpoints; only active-face support is used. -/
theorem stateMap_endpoint_persistence_on_support {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hW : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    {z : E × E} (hs : intervalSupported hH lo hi z.1)
    (hz : endpointStatePresent hH lo hi z) :
    endpointStatePresent hH lo hi (stateMap H W z) := by
  obtain ⟨hlo,hhi⟩ := weightedAlpha_strict_bounds_on_support hH hcomm hW ha hab hs hz.1
  refine ⟨hz.2,?_,?_⟩
  · change coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) lo ≠ 0
    rw [coordinates_step]
    apply smul_ne_zero _ hz.2.1
    exact ne_of_gt (sub_pos.mpr ((lt_div_iff ha).mp hhi))
  · change coordinates hH (z.2-weightedAlpha H W z.1 • H z.2) hi ≠ 0
    rw [coordinates_step]
    apply smul_ne_zero _ hz.2.2
    exact ne_of_lt (sub_neg.mpr ((div_lt_iff (ha.trans hab)).mp hlo))

theorem endpoint_state_persistence_on_support {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (W : ℕ → E →ₗ[ℝ] E) (hcomm : ∀ n, Function.Commute H (W n))
    (hW : ∀ n, ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (W n x))
    {lo hi : Eigenvalues H} (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    (z : ℕ → E × E) (hs : intervalStateSupported hH lo hi (z 0))
    (hz : endpointStatePresent hH lo hi (z 0))
    (hrec : ∀ n, z (n+1)=stateMap H (W n) (z n)) :
    ∀ n, endpointStatePresent hH lo hi (z n) := by
  have hsupport := trajectory_interval_supported hH W z hs hrec
  intro n
  induction n with
  | zero => exact hz
  | succ n ih =>
    rw [hrec]
    exact stateMap_endpoint_persistence_on_support hH (hcomm n) (hW n) ha hab (hsupport n).1 ih

end BB.Operator
