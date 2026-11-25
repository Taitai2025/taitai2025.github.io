import BB.SpectralPVM
import BB.EndpointAttainment
import BB.BorelMain

/-!
# Exact endpoint trajectories stated with the actual spectral projectors

The two endpoint components are E_A({r})g₀ and E_A({s})g₀. Spectral support
gives their sum, singleton projections give their eigenvalue equations, and
the source's projection norm balance gives the exact matched trajectory.
-/

noncomputable section
namespace BB
open MeasureTheory Set Filter
open scoped Topology
local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable (A : E →L[ℝ] E) (hA : A.toLinearMap.IsSymmetric) (a b : ℝ)
  (hbounds : ∀ x : E, a*‖x‖^2 ≤ ⟪x,A x⟫ ∧ ⟪x,A x⟫ ≤ b*‖x‖^2)

theorem operator_spectral_pvm_eq_self_of_ae (B : Set ℝ) (hB : MeasurableSet B) (x : E)
    (hsupport : ∀ᵐ (t : Icc a b) ∂(operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)),
      (t : ℝ) ∈ B) : (operatorSpectralPVM A hA a b hbounds).map B hB x = x := by
  have hmass : (operatorSpectralMeasure A hA a b hbounds x : Measure (Icc a b)) (Subtype.val ⁻¹' B) =
      ENNReal.ofReal (‖x‖^2) := by
    rw [← operator_spectral_measure_univ A hA a b hbounds x]
    exact (ae_mem_iff_measure_eq (hB.preimage measurable_subtype_coe).nullMeasurableSet).mp hsupport
  have hn := operator_spectral_pvm_norm_sq A hA a b hbounds B hB x
  have hi := spectral_projection_self A hA a b hbounds
    (Subtype.val ⁻¹' B) (hB.preimage measurable_subtype_coe) x
  change ⟪(operatorSpectralPVM A hA a b hbounds).map B hB x,x⟫ = _ at hi
  rw [hmass, ENNReal.toReal_ofReal (sq_nonneg _)] at hn hi
  have hz : ‖(operatorSpectralPVM A hA a b hbounds).map B hB x - x‖^2 = 0 := by
    rw [norm_sub_sq_real, hn, hi]
    ring
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

/-- The active support used in the main theorem gives literal projection
support, without assuming a spectral representation. -/
theorem operator_spectral_pvm_eq_self_of_active_support (B : Set ℝ)
    (hB : MeasurableSet B) (x : E) (hx : x ≠ 0)
    (hsupport : operatorActiveSupport A hA a b hbounds x hx ⊆ B) :
    (operatorSpectralPVM A hA a b hbounds).map B hB x = x := by
  apply operator_spectral_pvm_eq_self_of_ae A hA a b hbounds B hB x
  have hν : ∀ᵐ (t : Icc a b) ∂(operatorSpectralProbability A hA a b hbounds x hx : Measure (Icc a b)),
      (t : ℝ) ∈ B := (ae_mem_measureSupport _).mono (fun t ht => hsupport ⟨t,ht,rfl⟩)
  rw [operator_spectral_measure_nonzero A hA a b hbounds x hx]
  exact ae_smul_measure hν _

theorem operator_spectral_pvm_atom_eigenvector (r : spectrum ℝ A) (x : E) :
    A ((operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)} (measurableSet_singleton _) x) =
      (r : ℝ) • (operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)} (measurableSet_singleton _) x := by
  have hr : (r : ℝ) ∈ Icc a b := operator_spectrum_subset_form_interval A a b hbounds r.2
  rw [operator_spectral_pvm_singleton A hA a b hbounds (⟨r,hr⟩ : Icc a b)]
  exact spectral_projection_singleton_eigenvector A hA a b hbounds ⟨r,hr⟩ x

theorem operator_spectral_two_point_decomposition (r s : ℝ) (hrs : r ≠ s) (x : E)
    (hsupport : (operatorSpectralPVM A hA a b hbounds).map ({r} ∪ {s})
      ((measurableSet_singleton r).union (measurableSet_singleton s)) x = x) :
    (operatorSpectralPVM A hA a b hbounds).map {r} (measurableSet_singleton r) x +
      (operatorSpectralPVM A hA a b hbounds).map {s} (measurableSet_singleton s) x = x := by
  have hd : Disjoint ({r} : Set ℝ) {s} := disjoint_singleton.mpr hrs
  rw [(operatorSpectralPVM A hA a b hbounds).disjoint_union _ _
    (measurableSet_singleton r) (measurableSet_singleton s) hd] at hsupport
  exact hsupport

/-- Every actual matched BB1 trajectory satisfying the source's projector
support and equal endpoint energy conditions has the exact geometric norm. -/
theorem projected_endpoint_bb1_exact (r s : spectrum ℝ A)
    (hr : 0 < (r : ℝ)) (hrs : (r : ℝ) < s) (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hsupport : (operatorSpectralPVM A hA a b hbounds).map ({(r : ℝ)} ∪ {(s : ℝ)})
      ((measurableSet_singleton _).union (measurableSet_singleton _)) (g 0) = g 0)
    (hbalance : ‖(operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)}
        (measurableSet_singleton _) (g 0)‖^2 =
      ‖(operatorSpectralPVM A hA a b hbounds).map {(s : ℝ)} (measurableSet_singleton _) (g 0)‖^2)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap (operatorBB1 A.toLinearMap (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorBB1 A.toLinearMap (g n)) (g (n+1))) :
    (∀ n, ‖g n‖ = (rate (r : ℝ) (s : ℝ))^n*‖g 0‖) ∧
      operatorTrajectoryFactor g = rate (r : ℝ) (s : ℝ) := by
  let p := (operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)} (measurableSet_singleton _) (g 0)
  let q := (operatorSpectralPVM A hA a b hbounds).map {(s : ℝ)} (measurableSet_singleton _) (g 0)
  have hsum : p+q = g 0 := operator_spectral_two_point_decomposition A hA a b hbounds
    r s hrs.ne (g 0) hsupport
  have hbal : ‖p‖ = ‖q‖ := by change ‖p‖^2 = ‖q‖^2 at hbalance; nlinarith [norm_nonneg p,norm_nonneg q]
  have hp0 : p ≠ 0 := by
    intro hp
    have hq : q = 0 := norm_eq_zero.mp (by simpa only [hp,norm_zero] using hbal.symm)
    exact hg0 (by simpa only [hp,hq,add_zero] using hsum.symm)
  exact balanced_endpoint_trajectory_exact A.toLinearMap hA r s hr hrs p q
    (operator_spectral_pvm_atom_eigenvector A hA a b hbounds r (g 0))
    (operator_spectral_pvm_atom_eigenvector A hA a b hbounds s (g 0)) hp0 hbal
    g hsum.symm hfirst hupdate

/-- Projection balance for a fixed weight operator whose endpoint actions
are known. This includes every finite-dimensional positive spectral weight. -/
theorem projected_endpoint_weighted_exact (W : E →ₗ[ℝ] E)
    (r s : spectrum ℝ A) (wr ws : ℝ) (hwr : 0 < wr) (hws : 0 < ws)
    (hr : 0 < (r : ℝ)) (hrs : (r : ℝ) < s)
    (hWr : ∀ z, A z = (r : ℝ) • z → W z = wr • z)
    (hWs : ∀ z, A z = (s : ℝ) • z → W z = ws • z)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hsupport : (operatorSpectralPVM A hA a b hbounds).map ({(r : ℝ)} ∪ {(s : ℝ)})
      ((measurableSet_singleton _).union (measurableSet_singleton _)) (g 0) = g 0)
    (hbalance : wr * ‖(operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)}
        (measurableSet_singleton _) (g 0)‖^2 =
      ws * ‖(operatorSpectralPVM A hA a b hbounds).map {(s : ℝ)} (measurableSet_singleton _) (g 0)‖^2)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap W (g n)) (g (n+1))) :
    (∀ n, ‖g n‖ = (rate (r : ℝ) (s : ℝ))^n*‖g 0‖) ∧
      operatorTrajectoryFactor g = rate (r : ℝ) (s : ℝ) := by
  let p := (operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)} (measurableSet_singleton _) (g 0)
  let q := (operatorSpectralPVM A hA a b hbounds).map {(s : ℝ)} (measurableSet_singleton _) (g 0)
  have hsum : p+q = g 0 := operator_spectral_two_point_decomposition A hA a b hbounds
    r s hrs.ne (g 0) hsupport
  have hp := operator_spectral_pvm_atom_eigenvector A hA a b hbounds r (g 0)
  have hq := operator_spectral_pvm_atom_eigenvector A hA a b hbounds s (g 0)
  have hbal : wr*‖p‖^2 = ws*‖q‖^2 := hbalance
  have hp0 : p ≠ 0 := by
    intro hpzero
    have hqzero : q = 0 := by
      rw [hpzero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] at hbal
      have hn := (mul_eq_zero.mp hbal.symm).resolve_left hws.ne'
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact hg0 (by simpa only [hpzero,hqzero,add_zero] using hsum.symm)
  exact weighted_balanced_endpoint_trajectory_exact A.toLinearMap W hA r s wr ws hr hrs hwr
    p q hp hq (hWr p hp) (hWs q hq) hp0 hbal g hsum.symm hfirst hupdate

/-- The same literal projection balance yields exact trajectories for every
actual positive bounded Borel rule on the actual spectrum. -/
theorem projected_endpoint_borel_exact (Ψ : spectrum ℝ A → ℝ) (hΨ : Measurable Ψ)
    (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) (hΨbounds : ∀ t, l ≤ Ψ t ∧ Ψ t ≤ u)
    (r s : spectrum ℝ A) (hr : 0 < (r : ℝ)) (hrs : (r : ℝ) < s)
    (g : ℕ → E) (hg0 : g 0 ≠ 0)
    (hsupport : (operatorSpectralPVM A hA a b hbounds).map ({(r : ℝ)} ∪ {(s : ℝ)})
      ((measurableSet_singleton _).union (measurableSet_singleton _)) (g 0) = g 0)
    (hbalance : Ψ r * ‖(operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)}
        (measurableSet_singleton _) (g 0)‖^2 =
      Ψ s * ‖(operatorSpectralPVM A hA a b hbounds).map {(s : ℝ)} (measurableSet_singleton _) (g 0)‖^2)
    (hfirst : g 1 = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap (g 0)) (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep A.toLinearMap
      (operatorWeightedBB A.toLinearMap
        (spectralBorelOperator A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds).toLinearMap (g n)) (g (n+1))) :
    (∀ n, ‖g n‖ = (rate (r : ℝ) (s : ℝ))^n*‖g 0‖) ∧
      operatorTrajectoryFactor g = rate (r : ℝ) (s : ℝ) := by
  let p := (operatorSpectralPVM A hA a b hbounds).map {(r : ℝ)} (measurableSet_singleton _) (g 0)
  let q := (operatorSpectralPVM A hA a b hbounds).map {(s : ℝ)} (measurableSet_singleton _) (g 0)
  have hsum : p+q = g 0 := operator_spectral_two_point_decomposition A hA a b hbounds
    r s hrs.ne (g 0) hsupport
  have hp := operator_spectral_pvm_atom_eigenvector A hA a b hbounds r (g 0)
  have hq := operator_spectral_pvm_atom_eigenvector A hA a b hbounds s (g 0)
  have hbal : Ψ r*‖p‖^2 = Ψ s*‖q‖^2 := hbalance
  have hp0 : p ≠ 0 := by
    intro hpzero
    have hqzero : q = 0 := by
      rw [hpzero,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero] at hbal
      have hn := (mul_eq_zero.mp hbal.symm).resolve_left (hl.trans_le (hΨbounds s).1).ne'
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)
    exact hg0 (by simpa only [hpzero,hqzero,add_zero] using hsum.symm)
  exact weighted_balanced_endpoint_trajectory_exact A.toLinearMap _ hA r s (Ψ r) (Ψ s)
    hr hrs (hl.trans_le (hΨbounds r).1) p q hp hq
    (spectral_borel_operator_eigenvector A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds r p hp)
    (spectral_borel_operator_eigenvector A hA a b hbounds Ψ hΨ l u hl hlu hΨbounds s q hq)
    hp0 hbal g hsum.symm hfirst hupdate

end BB
