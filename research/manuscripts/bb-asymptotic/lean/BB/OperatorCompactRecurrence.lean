import BB.HilbertRestrictionDynamics
import BB.OperatorActiveSupport

/-!
# Spectral recurrence on every compact carrier

The original operator measure is constructed on a bounding interval. This file
restricts that actual measure to its intersection with an arbitrary compact
real set and pushes it into that set. The set may be disconnected or extend
beyond the operator's chosen bounding interval.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

def compactRealCoordinate (K : Set ℝ) : C(K,ℝ) := ⟨Subtype.val,continuous_subtype_val⟩

def intervalCarrier (a b : ℝ) (K : Set ℝ) : Set (Icc a b) := {t | (t : ℝ) ∈ K}

lemma interval_carrier_closed (a b : ℝ) (K : Set ℝ) [CompactSpace K] :
    IsClosed (intervalCarrier a b K) :=
  (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace K)).isClosed.preimage continuous_subtype_val

instance intervalCarrierCompact (a b : ℝ) (K : Set ℝ) [CompactSpace K] :
    CompactSpace (intervalCarrier a b K) :=
  isCompact_iff_compactSpace.mp (interval_carrier_closed a b K).isCompact

def intervalCarrierInclusion (a b : ℝ) (K : Set ℝ) : C(intervalCarrier a b K,K) :=
  ⟨fun t => ⟨t.1.1,t.2⟩,(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

def probabilityToCompact (a b : ℝ) (K : Set ℝ) [CompactSpace K]
    (ν : ProbabilityMeasure (Icc a b)) (hfull : ∀ᵐ (t : Icc a b) ∂(ν : Measure (Icc a b)), (t : ℝ) ∈ K) :
    ProbabilityMeasure K :=
  probabilityPush (intervalCarrierInclusion a b K)
    (probabilityOnClosed ν (intervalCarrier a b K) (interval_carrier_closed a b K) hfull)

def probabilityStateToCompact (a b : ℝ) (K : Set ℝ) [CompactSpace K]
    (χ : ProbabilityState (Icc a b))
    (hfull : (∀ᵐ (t : Icc a b) ∂(χ.1 : Measure (Icc a b)), (t : ℝ) ∈ K) ∧
      (∀ᵐ (t : Icc a b) ∂(χ.2 : Measure (Icc a b)), (t : ℝ) ∈ K)) : ProbabilityState K :=
  (probabilityToCompact a b K χ.1 hfull.1,probabilityToCompact a b K χ.2 hfull.2)

lemma probability_state_to_compact_congr (a b : ℝ) (K : Set ℝ) [CompactSpace K]
    (χ ψ : ProbabilityState (Icc a b)) (he : χ = ψ)
    (hχ : (∀ᵐ (t : Icc a b) ∂(χ.1 : Measure (Icc a b)), (t : ℝ) ∈ K) ∧
      (∀ᵐ (t : Icc a b) ∂(χ.2 : Measure (Icc a b)), (t : ℝ) ∈ K))
    (hψ : (∀ᵐ (t : Icc a b) ∂(ψ.1 : Measure (Icc a b)), (t : ℝ) ∈ K) ∧
      (∀ᵐ (t : Icc a b) ∂(ψ.2 : Measure (Icc a b)), (t : ℝ) ∈ K)) :
    probabilityStateToCompact a b K χ hχ = probabilityStateToCompact a b K ψ hψ := by
  subst ψ
  rfl

lemma probability_to_compact_growth (a b : ℝ) (K : Set ℝ) [CompactSpace K]
    (χ : ProbabilityState (Icc a b))
    (hfull : (∀ᵐ (t : Icc a b) ∂(χ.1 : Measure (Icc a b)), (t : ℝ) ∈ K) ∧
      (∀ᵐ (t : Icc a b) ∂(χ.2 : Measure (Icc a b)), (t : ℝ) ∈ K)) :
    probabilityGrowth (compactRealCoordinate K) (probabilityStateToCompact a b K χ hfull) =
      probabilityGrowth (intervalCoordinate a b) χ := by
  change probabilityGrowth (compactRealCoordinate K)
    (probabilityStatePush (intervalCarrierInclusion a b K)
      (probabilityStateOnClosed (intervalCarrier a b K) (interval_carrier_closed a b K) χ hfull)) = _
  rw [probability_growth_push]
  exact probability_growth_on_closed (intervalCarrier a b K) (interval_carrier_closed a b K)
    (intervalCoordinate a b) χ hfull

lemma probability_to_compact_map (a b : ℝ) (K : Set ℝ) [CompactSpace K]
    (χ : ProbabilityState (Icc a b))
    (hfull : (∀ᵐ (t : Icc a b) ∂(χ.1 : Measure (Icc a b)), (t : ℝ) ∈ K) ∧
      (∀ᵐ (t : Icc a b) ∂(χ.2 : Measure (Icc a b)), (t : ℝ) ∈ K)) :
    probabilityStateToCompact a b K (probabilityMap (intervalCoordinate a b) χ)
      (probability_map_carried (intervalCarrier a b K) (intervalCoordinate a b) χ hfull) =
      probabilityMap (compactRealCoordinate K) (probabilityStateToCompact a b K χ hfull) := by
  change probabilityStatePush (intervalCarrierInclusion a b K)
    (probabilityStateOnClosed (intervalCarrier a b K) (interval_carrier_closed a b K)
      (probabilityMap (intervalCoordinate a b) χ)
      (probability_map_carried (intervalCarrier a b K) (intervalCoordinate a b) χ hfull)) =
    probabilityMap (compactRealCoordinate K)
      (probabilityStatePush (intervalCarrierInclusion a b K)
        (probabilityStateOnClosed (intervalCarrier a b K) (interval_carrier_closed a b K) χ hfull))
  rw [probability_map_push,probability_map_on_closed]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma operator_spectral_carried_of_support (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) (K : Set ℝ)
    (hs : operatorActiveSupport A hA a b hbounds x hx ⊆ K) :
    ∀ᵐ (t : Icc a b) ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)), (t : ℝ) ∈ K := by
  filter_upwards [ae_mem_measureSupport (operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b))] with t ht
  exact hs ⟨t,ht,rfl⟩

def operatorCompactProbability (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (K : Set ℝ) [CompactSpace K] (x : E) (hx : x ≠ 0)
    (hs : operatorActiveSupport A hA a b hbounds x hx ⊆ K) : ProbabilityMeasure K :=
  probabilityToCompact a b K (operatorSpectralProbability A hA a b hbounds x hx)
    (operator_spectral_carried_of_support A hA a b hbounds x hx K hs)

lemma operator_active_support_congr (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x y : E) (hx : x ≠ 0) (hy : y ≠ 0) (he : x = y) :
    operatorActiveSupport A hA a b hbounds x hx = operatorActiveSupport A hA a b hbounds y hy := by
  subst y
  rfl

lemma operator_compact_probability_congr (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (K : Set ℝ) [CompactSpace K] (x y : E) (hx : x ≠ 0) (hy : y ≠ 0)
    (hxs : operatorActiveSupport A hA a b hbounds x hx ⊆ K)
    (hys : operatorActiveSupport A hA a b hbounds y hy ⊆ K) (he : x = y) :
    operatorCompactProbability A hA a b hbounds K x hx hxs =
      operatorCompactProbability A hA a b hbounds K y hy hys := by
  subst y
  rfl

lemma operator_active_step_support_subset (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (x : E) (hx : x ≠ 0) (α : ℝ) (hy : operatorGradientStep A.toLinearMap α x ≠ 0) :
    operatorActiveSupport A hA a b hbounds (operatorGradientStep A.toLinearMap α x) hy ⊆
      operatorActiveSupport A hA a b hbounds x hx := by
  exact Set.image_subset _ (operator_spectral_step_support_subset A hA a b hbounds x hx α hy)

theorem operator_compact_spectral_pair_update (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (K : Set ℝ) [CompactSpace K] (x z : E) (hx : x ≠ 0) (hz : z ≠ 0)
    (hxs : operatorActiveSupport A hA a b hbounds x hx ⊆ K)
    (hzs : operatorActiveSupport A hA a b hbounds z hz ⊆ K)
    (hy : operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x ≠ 0) :
    (operatorCompactProbability A hA a b hbounds K
       (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x) hy
       ((operator_active_step_support_subset A hA a b hbounds x hx _ hy).trans hxs),
      operatorCompactProbability A hA a b hbounds K x hx hxs) =
      probabilityMap (compactRealCoordinate K)
        (operatorCompactProbability A hA a b hbounds K x hx hxs,
         operatorCompactProbability A hA a b hbounds K z hz hzs) := by
  let χ := operatorSpectralPair A hA a b hbounds x z hx hz
  have hfull := And.intro (operator_spectral_carried_of_support A hA a b hbounds x hx K hxs)
    (operator_spectral_carried_of_support A hA a b hbounds z hz K hzs)
  have he := probability_to_compact_map a b K χ hfull
  have hys := (operator_active_step_support_subset A hA a b hbounds x hx _ hy).trans hxs
  have hnew := And.intro
    (operator_spectral_carried_of_support A hA a b hbounds
      (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x) hy K hys)
    (operator_spectral_carried_of_support A hA a b hbounds x hx K hxs)
  exact (probability_state_to_compact_congr a b K _ _
    (operator_spectral_pair_update A hA a b hbounds x z hx hz hy) hnew
    (probability_map_carried (intervalCarrier a b K) (intervalCoordinate a b) χ hfull)).trans he

theorem operator_compact_spectral_norm_ratio (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (K : Set ℝ) [CompactSpace K] (x z : E) (hx : x ≠ 0) (hz : z ≠ 0)
    (hxs : operatorActiveSupport A hA a b hbounds x hx ⊆ K)
    (hzs : operatorActiveSupport A hA a b hbounds z hz ⊆ K) :
    ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap z) x‖/‖x‖ =
      probabilityGrowth (compactRealCoordinate K)
        (operatorCompactProbability A hA a b hbounds K x hx hxs,
         operatorCompactProbability A hA a b hbounds K z hz hzs) := by
  rw [operator_spectral_pair_norm_ratio]
  exact (probability_to_compact_growth a b K (operatorSpectralPair A hA a b hbounds x z hx hz)
    ⟨operator_spectral_carried_of_support A hA a b hbounds x hx K hxs,
     operator_spectral_carried_of_support A hA a b hbounds z hz K hzs⟩).symm

lemma operator_bb1_nonzero_predecessor (A : E →L[ℝ] E) (g : ℕ → E) (α₀ : ℝ)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1)))
    (n : ℕ) (hn : g (n+1) ≠ 0) : g n ≠ 0 := by
  intro hz
  apply hn
  cases n with
  | zero => simpa only [hz,operatorGradientStep,map_zero,smul_zero,sub_self] using hfirst
  | succ n => simpa only [hz,operatorGradientStep,map_zero,smul_zero,sub_self] using hupdate n

theorem operator_bb1_active_support_persistent (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (α₀ : ℝ)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    ∀ (n : ℕ) (hn : g n ≠ 0), operatorActiveSupport A hA a b hbounds (g n) hn ⊆
      operatorActiveSupport A hA a b hbounds (g 0) hg0 := by
  intro n
  induction n with
  | zero => intro _; exact Subset.rfl
  | succ n ih =>
    intro hn
    have hp := operator_bb1_nonzero_predecessor A g α₀ hfirst hupdate n hn
    apply Set.Subset.trans _ (ih hp)
    cases n with
    | zero =>
      have hy : operatorGradientStep A.toLinearMap α₀ (g 0) ≠ 0 := hfirst ▸ hn
      rw [operator_active_support_congr A hA a b hbounds (g 1) _ hn hy hfirst]
      exact operator_active_step_support_subset A hA a b hbounds (g 0) hp α₀ hy
    | succ n =>
      have hy : operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g n)) (g (n+1)) ≠ 0 :=
        hupdate n ▸ hn
      rw [operator_active_support_congr A hA a b hbounds (g (n+2)) _ hn hy (hupdate n)]
      exact operator_active_step_support_subset A hA a b hbounds
        (g (n+1)) hp (operatorBB1 A.toLinearMap (g n)) hy

/-- On any compact set containing the initial active support, consecutive
nonzero gradients satisfy the source recurrence and its actual norm ratio.
The preceding gradient is proved nonzero, rather than assumed nonzero. -/
theorem operator_compact_orbit_recurrence (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (g : ℕ → E) (hg0 : g 0 ≠ 0) (α₀ : ℝ)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1)))
    (K : Set ℝ) [CompactSpace K]
    (hK : operatorActiveSupport A hA a b hbounds (g 0) hg0 ⊆ K)
    (n : ℕ) (hcurrent : g (n+1) ≠ 0) (hnext : g (n+2) ≠ 0) :
    ∃ (hprevious : g n ≠ 0)
      (hs : ∀ (j : ℕ) (hj : g j ≠ 0), operatorActiveSupport A hA a b hbounds (g j) hj ⊆ K),
      let νprev := operatorCompactProbability A hA a b hbounds K (g n) hprevious (hs n hprevious)
      let νcur := operatorCompactProbability A hA a b hbounds K (g (n+1)) hcurrent (hs (n+1) hcurrent)
      let νnext := operatorCompactProbability A hA a b hbounds K (g (n+2)) hnext (hs (n+2) hnext)
      (νnext,νcur) = probabilityMap (compactRealCoordinate K) (νcur,νprev) ∧
      ‖g (n+2)‖/‖g (n+1)‖ = probabilityGrowth (compactRealCoordinate K) (νcur,νprev) := by
  have hp := operator_bb1_nonzero_predecessor A g α₀ hfirst hupdate n hcurrent
  have hs : ∀ (j : ℕ) (hj : g j ≠ 0), operatorActiveSupport A hA a b hbounds (g j) hj ⊆ K :=
    fun j hj => (operator_bb1_active_support_persistent A hA a b hbounds g hg0 α₀ hfirst hupdate j hj).trans hK
  refine ⟨hp,hs,?_⟩
  dsimp only
  have hy : operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g n)) (g (n+1)) ≠ 0 :=
    hupdate n ▸ hnext
  constructor
  · have hys := (operator_active_step_support_subset A hA a b hbounds
      (g (n+1)) hcurrent (operatorBB1 A.toLinearMap (g n)) hy).trans (hs _ hcurrent)
    rw [operator_compact_probability_congr A hA a b hbounds K (g (n+2)) _ hnext hy
      (hs _ hnext) hys (hupdate n)]
    exact operator_compact_spectral_pair_update A hA a b hbounds K
      (g (n+1)) (g n) hcurrent hp (hs _ hcurrent) (hs _ hp) hy
  · calc
      ‖g (n+2)‖/‖g (n+1)‖ =
          ‖operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g n)) (g (n+1))‖/‖g (n+1)‖ :=
        congrArg (fun x : E => ‖x‖/‖g (n+1)‖) (hupdate n)
      _ = _ := operator_compact_spectral_norm_ratio A hA a b hbounds K
        (g (n+1)) (g n) hcurrent hp (hs _ hcurrent) (hs _ hp)

/-- Matched initialization starts at the diagonal pair; a regular first step
is exactly its image under the same compact-carrier probability map. -/
theorem operator_compact_matched_start (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric)
    (a b : ℝ) (hbounds : ∀ y : E, a*‖y‖^2 ≤ ⟪y,A y⟫ ∧ ⟪y,A y⟫ ≤ b*‖y‖^2)
    (K : Set ℝ) [CompactSpace K] (x : E) (hx : x ≠ 0)
    (hs : operatorActiveSupport A hA a b hbounds x hx ⊆ K)
    (hy : operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap x) x ≠ 0) :
    (operatorCompactProbability A hA a b hbounds K
       (operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap x) x) hy
       ((operator_active_step_support_subset A hA a b hbounds x hx _ hy).trans hs),
     operatorCompactProbability A hA a b hbounds K x hx hs) =
      probabilityMap (compactRealCoordinate K)
        (operatorCompactProbability A hA a b hbounds K x hx hs,
         operatorCompactProbability A hA a b hbounds K x hx hs) :=
  operator_compact_spectral_pair_update A hA a b hbounds K x x hx hx hs hs hy

end BB
