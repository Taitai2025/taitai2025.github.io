import BB.ActiveSupport
import BB.LinearCoordinates
import Mathlib.Data.Finset.Sort

/-!
# One coordinate for each distinct active eigenvalue

Coordinates with the same eigenvalue receive exactly the same scalar multiplier
at every step. Their initial squared amplitudes are grouped before taking a
square root. This preserves the sign of each later multiplier, the entire BB
quotient sequence, and every gradient norm. The final model is indexed in
strictly increasing spectral order.
-/

namespace BB
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def activeValues (lam g₀ : ι → ℝ) : Finset ℝ := (coordinateSupport g₀).image lam

def activeMass (lam g₀ : ι → ℝ) (r : ℝ) : ℝ :=
  ∑ i ∈ (coordinateSupport g₀).filter (fun i => lam i = r), (g₀ i)^2

lemma active_mass_nonneg (lam g₀ : ι → ℝ) (r : ℝ) : 0 ≤ activeMass lam g₀ r :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma active_mass_pos (lam g₀ : ι → ℝ) {r : ℝ} (hr : r ∈ activeValues lam g₀) :
    0 < activeMass lam g₀ r := by
  obtain ⟨i, hi, hir⟩ := Finset.mem_image.mp hr
  apply Finset.sum_pos' (fun _ _ => sq_nonneg _)
  refine ⟨i, Finset.mem_filter.mpr ⟨hi,hir⟩, ?_⟩
  exact sq_pos_of_ne_zero ((Finset.mem_filter.mp hi).2)

lemma sum_over_coordinate_support (g₀ f : ι → ℝ)
    (hf : ∀ i, g₀ i = 0 → f i = 0) : ∑ i ∈ coordinateSupport g₀, f i = ∑ i, f i := by
  apply Finset.sum_filter_of_ne
  intro i _ hi
  exact fun hz => hi (hf i hz)

def groupedVector (lam g₀ : ι → ℝ) (p : ℝ → ℝ) (r : activeValues lam g₀) : ℝ :=
  p r * Real.sqrt (activeMass lam g₀ r)

lemma grouped_weighted_energy (lam g₀ : ι → ℝ) (p ψ : ℝ → ℝ) :
    (∑ r : activeValues lam g₀, ψ r * (groupedVector lam g₀ p r)^2) =
      ∑ i, ψ (lam i) * (p (lam i) * g₀ i)^2 := by
  have hgroup :
      (∑ r : activeValues lam g₀, ψ r * (groupedVector lam g₀ p r)^2) =
        ∑ r ∈ activeValues lam g₀, ∑ i ∈ (coordinateSupport g₀).filter (fun i => lam i = r),
          ψ (lam i) * (p (lam i) * g₀ i)^2 := by
    unfold groupedVector
    simp_rw [mul_pow, Real.sq_sqrt (active_mass_nonneg lam g₀ _)]
    rw [Finset.sum_coe_sort (activeValues lam g₀)
      (fun r => ψ r * ((p r)^2 * activeMass lam g₀ r))]
    apply Finset.sum_congr rfl
    intro r _
    unfold activeMass
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [(Finset.mem_filter.mp hi).2]
  rw [hgroup, Finset.sum_fiberwise_of_maps_to
    (s := coordinateSupport g₀) (t := activeValues lam g₀) (g := lam)
    (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)]
  apply sum_over_coordinate_support
  intro i hi
  simp [hi]

lemma grouped_energy (lam g₀ : ι → ℝ) (p : ℝ → ℝ) :
    energy (groupedVector lam g₀ p) = energy (fun i => p (lam i)*g₀ i) := by
  simpa only [energy, one_mul] using grouped_weighted_energy lam g₀ p (fun _ => 1)

lemma grouped_norm (lam g₀ : ι → ℝ) (p : ℝ → ℝ) :
    normDiag (groupedVector lam g₀ p) = normDiag (fun i => p (lam i)*g₀ i) := by
  unfold normDiag
  rw [grouped_energy]

lemma grouped_quotient (lam g₀ : ι → ℝ) (p : ℝ → ℝ) :
    diagonalBB1 (fun r : activeValues lam g₀ => (r:ℝ)) (groupedVector lam g₀ p) =
      diagonalBB1 lam (fun i => p (lam i)*g₀ i) := by
  unfold diagonalBB1
  rw [grouped_energy, grouped_weighted_energy lam g₀ p (fun r => r)]

def scalarMultiplier (α : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => fun _ => 1
  | n+1 => fun r => (1-α n*r)*scalarMultiplier α n r

lemma trajectory_scalar_factorization (lam : ι → ℝ) (α : ℕ → ℝ) (g : ℕ → ι → ℝ)
    (hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n)) (n : ℕ) :
    g n = fun i => scalarMultiplier α n (lam i)*g 0 i := by
  induction n with
  | zero => funext i; simp [scalarMultiplier]
  | succ n ih =>
    rw [hstep n, ih]
    funext i
    simp only [gradientUpdate, scalarMultiplier]
    ring

def groupedTrajectory (lam g₀ : ι → ℝ) (α : ℕ → ℝ) (n : ℕ) : activeValues lam g₀ → ℝ :=
  groupedVector lam g₀ (scalarMultiplier α n)

lemma grouped_trajectory_initial_pos (lam g₀ : ι → ℝ) (α : ℕ → ℝ)
    (r : activeValues lam g₀) : 0 < groupedTrajectory lam g₀ α 0 r := by
  simp only [groupedTrajectory, groupedVector, scalarMultiplier, one_mul]
  exact Real.sqrt_pos.mpr (active_mass_pos lam g₀ r.2)

lemma grouped_trajectory_step (lam g₀ : ι → ℝ) (α : ℕ → ℝ) (n : ℕ) :
    groupedTrajectory lam g₀ α (n+1) = gradientUpdate
      (fun r : activeValues lam g₀ => (r:ℝ)) (α n) (groupedTrajectory lam g₀ α n) := by
  funext r
  simp only [groupedTrajectory, groupedVector, scalarMultiplier, gradientUpdate]
  ring

lemma grouped_trajectory_norm (lam : ι → ℝ) (α : ℕ → ℝ) (g : ℕ → ι → ℝ)
    (hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n)) (n : ℕ) :
    normDiag (groupedTrajectory lam (g 0) α n) = normDiag (g n) := by
  rw [trajectory_scalar_factorization lam α g hstep n]
  exact grouped_norm lam (g 0) (scalarMultiplier α n)

lemma grouped_trajectory_quotient (lam : ι → ℝ) (α : ℕ → ℝ) (g : ℕ → ι → ℝ)
    (hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n)) (n : ℕ) :
    diagonalBB1 (fun r : activeValues lam (g 0) => (r:ℝ))
      (groupedTrajectory lam (g 0) α n) = diagonalBB1 lam (g n) := by
  rw [trajectory_scalar_factorization lam α g hstep n]
  exact grouped_quotient lam (g 0) (scalarMultiplier α n)

lemma grouped_trajectory_reconstruction (lam : ι → ℝ) (α : ℕ → ℝ) (g : ℕ → ι → ℝ)
    (hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n))
    (i : ι) (hi : g 0 i ≠ 0) (n : ℕ) :
    let r : activeValues lam (g 0) := ⟨lam i,
      Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩, rfl⟩⟩
    g n i = groupedTrajectory lam (g 0) α n r * g 0 i /
      Real.sqrt (activeMass lam (g 0) (lam i)) := by
  dsimp
  have hmem : lam i ∈ activeValues lam (g 0) :=
    Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩, rfl⟩
  have hn := (Real.sqrt_pos.mpr (active_mass_pos lam (g 0) hmem)).ne'
  rw [trajectory_scalar_factorization lam α g hstep n]
  simp only [groupedTrajectory, groupedVector]
  field_simp
  ring

def orderedActiveEigenvalue (lam g₀ : ι → ℝ) : Fin (activeValues lam g₀).card → ℝ :=
  (activeValues lam g₀).orderEmbOfFin rfl

def orderedActiveTrajectory (lam g₀ : ι → ℝ) (α : ℕ → ℝ) (n : ℕ)
    (i : Fin (activeValues lam g₀).card) : ℝ :=
  groupedTrajectory lam g₀ α n ((activeValues lam g₀).orderIsoOfFin rfl i)

lemma ordered_active_strictMono (lam g₀ : ι → ℝ) : StrictMono (orderedActiveEigenvalue lam g₀) :=
  ((activeValues lam g₀).orderEmbOfFin rfl).strictMono

lemma ordered_active_range (lam g₀ : ι → ℝ) :
    Set.range (orderedActiveEigenvalue lam g₀) = (activeValues lam g₀ : Set ℝ) :=
  Finset.range_orderEmbOfFin _ _

lemma ordered_active_energy (lam g₀ : ι → ℝ) (α : ℕ → ℝ) (n : ℕ) :
    energy (orderedActiveTrajectory lam g₀ α n) = energy (groupedTrajectory lam g₀ α n) := by
  exact ((activeValues lam g₀).orderIsoOfFin rfl).toEquiv.sum_comp
    (fun r => (groupedTrajectory lam g₀ α n r)^2)

lemma ordered_active_norm (lam : ι → ℝ) (α : ℕ → ℝ) (g : ℕ → ι → ℝ)
    (hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n)) (n : ℕ) :
    normDiag (orderedActiveTrajectory lam (g 0) α n) = normDiag (g n) := by
  calc
    _ = normDiag (groupedTrajectory lam (g 0) α n) := congrArg Real.sqrt (ordered_active_energy _ _ _ _)
    _ = _ := grouped_trajectory_norm lam α g hstep n

lemma ordered_active_quotient (lam : ι → ℝ) (α : ℕ → ℝ) (g : ℕ → ι → ℝ)
    (hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n)) (n : ℕ) :
    diagonalBB1 (orderedActiveEigenvalue lam (g 0)) (orderedActiveTrajectory lam (g 0) α n) =
      diagonalBB1 lam (g n) := by
  rw [← grouped_trajectory_quotient lam α g hstep n]
  unfold diagonalBB1
  rw [ordered_active_energy]
  congr 1
  exact ((activeValues lam (g 0)).orderIsoOfFin rfl).toEquiv.sum_comp
    (fun r => (r:ℝ)*(groupedTrajectory lam (g 0) α n r)^2)

lemma ordered_active_step (lam g₀ : ι → ℝ) (α : ℕ → ℝ) (n : ℕ) :
    orderedActiveTrajectory lam g₀ α (n+1) = gradientUpdate
      (orderedActiveEigenvalue lam g₀) (α n) (orderedActiveTrajectory lam g₀ α n) := by
  funext i
  exact congrFun (grouped_trajectory_step lam g₀ α n)
    ((activeValues lam g₀).orderIsoOfFin rfl i)

lemma active_values_nonempty (lam g₀ : ι → ℝ) (hg₀ : 0 < energy g₀) :
    (activeValues lam g₀).Nonempty := by
  have hne : g₀ ≠ 0 := fun hz => (ne_of_gt hg₀) ((energy_eq_zero_iff g₀).mpr hz)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hne
  refine ⟨lam i, Finset.mem_image.mpr ⟨i,?_,rfl⟩⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,hi⟩

/-- Exact sorted reduction, including every later iterate and every delayed
quotient. Repeated original eigenvalues produce exactly one new coordinate. -/
theorem distinct_active_reduction (lam : ι → ℝ) (g : ℕ → ι → ℝ) (α₀ : ℝ)
    (hg₀ : 0 < energy (g 0)) (hlam : ∀ i, g 0 i ≠ 0 → 0 < lam i)
    (hfirst : g 1 = gradientUpdate lam α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1))) :
    ∃ (d : ℕ) (mu : Fin d → ℝ) (q : ℕ → Fin d → ℝ),
      0 < d ∧ StrictMono mu ∧ (∀ i, 0 < mu i ∧ 0 < q 0 i) ∧
      Set.range mu = (activeValues lam (g 0) : Set ℝ) ∧
      (∀ n, normDiag (q n) = normDiag (g n)) ∧
      (∀ n, diagonalBB1 mu (q n) = diagonalBB1 lam (g n)) ∧
      q 1 = gradientUpdate mu α₀ (q 0) ∧
      (∀ n, q (n+2) = gradientUpdate mu (diagonalBB1 mu (q n)) (q (n+1))) ∧
      rootFactor (fun n => normDiag (q n)/normDiag (q 0)) =
        rootFactor (fun n => normDiag (g n)/normDiag (g 0)) := by
  let α : ℕ → ℝ := fun n => match n with
    | 0 => α₀
    | k+1 => diagonalBB1 lam (g k)
  have hstep : ∀ n, g (n+1) = gradientUpdate lam (α n) (g n) := by
    intro n
    cases n with
    | zero => exact hfirst
    | succ k => exact hupdate k
  let mu := orderedActiveEigenvalue lam (g 0)
  let q := orderedActiveTrajectory lam (g 0) α
  have hn : ∀ n, normDiag (q n) = normDiag (g n) := ordered_active_norm lam α g hstep
  have hq : ∀ n, diagonalBB1 mu (q n) = diagonalBB1 lam (g n) :=
    ordered_active_quotient lam α g hstep
  refine ⟨(activeValues lam (g 0)).card,mu,q,
    Finset.card_pos.mpr (active_values_nonempty lam (g 0) hg₀),
    ordered_active_strictMono lam (g 0),?_,ordered_active_range lam (g 0),hn,hq,?_,?_,?_⟩
  · intro i
    constructor
    · change 0 < (((activeValues lam (g 0)).orderIsoOfFin rfl i) : ℝ)
      obtain ⟨j,hj,he⟩ := Finset.mem_image.mp ((activeValues lam (g 0)).orderIsoOfFin rfl i).2
      rw [← he]
      exact hlam j (Finset.mem_filter.mp hj).2
    · exact grouped_trajectory_initial_pos lam (g 0) α _
  · exact ordered_active_step lam (g 0) α 0
  · intro n
    rw [hq n]
    exact ordered_active_step lam (g 0) α (n+1)
  · congr 1
    funext n
    rw [hn n, hn 0]

section Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual symmetric-operator trajectory is first expressed in an
orthonormal eigenbasis and then grouped by distinct active eigenvalues. -/
theorem operator_distinct_active_reduction {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (a b α₀ : ℝ) (ha : 0 < a)
    (hbounds : ∀ x : E, a*‖x‖^2 ≤ inner (𝕜 := ℝ) x (H x) ∧
      inner (𝕜 := ℝ) x (H x) ≤ b*‖x‖^2)
    (g : ℕ → E) (hg₀ : g 0 ≠ 0)
    (hfirst : g 1 = operatorGradientStep H α₀ (g 0))
    (hupdate : ∀ n, g (n+2) = operatorGradientStep H (operatorBB1 H (g n)) (g (n+1))) :
    ∃ (d : ℕ) (mu : Fin d → ℝ) (q : ℕ → Fin d → ℝ),
      0 < d ∧ StrictMono mu ∧ (∀ i, 0 < mu i ∧ 0 < q 0 i) ∧
      Set.range mu = (activeValues (eigenValues hH) (eigenCoordinates hH (g 0)) : Set ℝ) ∧
      (∀ n, normDiag (q n) = ‖g n‖) ∧
      (∀ n, diagonalBB1 mu (q n) = operatorBB1 H (g n)) ∧
      q 1 = gradientUpdate mu α₀ (q 0) ∧
      (∀ n, q (n+2) = gradientUpdate mu (diagonalBB1 mu (q n)) (q (n+1))) ∧
      rootFactor (fun n => normDiag (q n)/normDiag (q 0)) =
        rootFactor (fun n => ‖g n‖/‖g 0‖) := by
  let v : ℕ → Fin (FiniteDimensional.finrank ℝ E) → ℝ := fun n => eigenCoordinates hH (g n)
  have hv₀ : 0 < energy (v 0) := by
    change 0 < energy (eigenCoordinates hH (g 0))
    rw [eigen_coordinates_energy]
    exact sq_pos_of_pos (norm_pos_iff.mpr hg₀)
  have hl : ∀ i, v 0 i ≠ 0 → 0 < eigenValues hH i :=
    fun i _ => ha.trans_le (eigenvalue_bounds hH a b hbounds i).1
  have hf : v 1 = gradientUpdate (eigenValues hH) α₀ (v 0) := by
    dsimp [v]
    rw [hfirst, eigen_coordinates_update]
  obtain ⟨d,mu,q,hd,hmono,hpos,hrange,hn,hq,hfirstq,hupdateq,hroot⟩ :=
    distinct_active_reduction (eigenValues hH) v α₀ hv₀ hl hf
      (eigen_coordinates_delayed_orbit hH g hupdate)
  refine ⟨d,mu,q,hd,hmono,hpos,hrange,?_,?_,hfirstq,hupdateq,?_⟩
  · intro n
    exact (hn n).trans (eigen_coordinates_norm hH (g n))
  · intro n
    exact (hq n).trans (eigen_coordinates_quotient hH (g n)).symm
  · simpa only [v, eigen_coordinates_norm] using hroot

end Operator

end
end BB
