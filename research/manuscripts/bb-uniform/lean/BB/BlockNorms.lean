import BB.BlockLift

set_option autoImplicit false

namespace BB.Blocks
open BB.Spectral
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

/-- Euclidean combination of the block norms. -/
noncomputable def blockL2 (u : ∀ i, E i) : ℝ := Real.sqrt (∑ i, ‖u i‖^2)

/-- Euclidean pair norm in block coordinates. -/
noncomputable def stateL2 (z : BState E) : ℝ :=
  Real.sqrt ((∑ i, ‖z.1 i‖^2) + (∑ i, ‖z.2 i‖^2))

def l2Cone (M : ℝ) (z : BState E) : Prop := blockL2 z.2 ≤ M*blockL2 z.1

@[simp] theorem blockL2_nonneg (u : ∀ i, E i) : 0 ≤ blockL2 u := Real.sqrt_nonneg _
@[simp] theorem stateL2_nonneg (z : BState E) : 0 ≤ stateL2 z := Real.sqrt_nonneg _

@[simp] theorem blockL2_sq (u : ∀ i, E i) : (blockL2 u)^2 = ∑ i, ‖u i‖^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))

@[simp] theorem stateL2_sq (z : BState E) :
    (stateL2 z)^2 = (∑ i, ‖z.1 i‖^2) + (∑ i, ‖z.2 i‖^2) :=
  Real.sq_sqrt (add_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    (Finset.sum_nonneg (fun i _ => sq_nonneg _)))

/-- The sup norm is dominated by the Euclidean block norm. -/
theorem norm_le_blockL2 (u : ∀ i, E i) : ‖u‖ ≤ blockL2 u := by
  apply (Real.le_sqrt (norm_nonneg _) (Finset.sum_nonneg (fun i _ => sq_nonneg _))).mpr
  simpa only [radius_norm,radius] using sum_sq_ge_norm_sq (radius u)

/-- Squared Euclidean norm is bounded using only the number of blocks. -/
theorem sum_norm_sq_bound (u : ∀ i, E i) :
    (∑ i, ‖u i‖^2) ≤ (Fintype.card ι : ℝ)*‖u‖^2 := by
  calc
    _ ≤ ∑ _i : ι, ‖u‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith only [norm_le_pi_norm u i,norm_nonneg (u i),norm_nonneg u]
    _ = _ := by simp

/-- The dimension factor counts distinct blocks, not block multiplicities. -/
theorem blockL2_le (u : ∀ i, E i) :
    blockL2 u ≤ Real.sqrt (Fintype.card ι : ℝ)*‖u‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _),?_⟩
  have hn : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  calc
    _ ≤ (Fintype.card ι : ℝ)*‖u‖^2 := sum_norm_sq_bound u
    _ = (Real.sqrt (Fintype.card ι : ℝ)*‖u‖)^2 := by rw [mul_pow,Real.sq_sqrt hn]

/-- The manuscript's Euclidean pair norm dominates the max-block state norm. -/
theorem norm_le_stateL2 (z : BState E) : ‖z‖ ≤ stateL2 z := by
  rw [Prod.norm_def]
  apply max_le
  · calc
      ‖z.1‖ ≤ blockL2 z.1 := norm_le_blockL2 _
      _ ≤ stateL2 z := Real.sqrt_le_sqrt (by
        have h : 0 ≤ ∑ i, ‖z.2 i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
        linarith only [h])
  · calc
      ‖z.2‖ ≤ blockL2 z.2 := norm_le_blockL2 _
      _ ≤ stateL2 z := Real.sqrt_le_sqrt (by
        have h : 0 ≤ ∑ i, ‖z.1 i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
        linarith only [h])

/-- Exact multiplicity-independent norm comparison for the pair. -/
theorem stateL2_le (z : BState E) :
    stateL2 z ≤ Real.sqrt (2*(Fintype.card ι : ℝ))*‖z‖ := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _),?_⟩
  have hn : 0 ≤ (Fintype.card ι : ℝ) := by positivity
  have h1 : ‖z.1‖^2 ≤ ‖z‖^2 := by
    nlinarith only [norm_fst_le z,norm_nonneg z.1,norm_nonneg z]
  have h2 : ‖z.2‖^2 ≤ ‖z‖^2 := by
    nlinarith only [norm_snd_le z,norm_nonneg z.2,norm_nonneg z]
  have hsum1 := (sum_norm_sq_bound z.1).trans (mul_le_mul_of_nonneg_left h1 hn)
  have hsum2 := (sum_norm_sq_bound z.2).trans (mul_le_mul_of_nonneg_left h2 hn)
  rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ 2*(Fintype.card ι : ℝ))]
  nlinarith only [hsum1,hsum2]

/-- Euclidean admissible pairs enter a slightly enlarged sup-norm cone. -/
theorem l2Cone_implies_blockCone {M : ℝ} (hM : 0 ≤ M) {z : BState E}
    (hz : l2Cone M z) : blockCone (M*Real.sqrt (Fintype.card ι : ℝ)) z := by
  unfold blockCone
  calc
    ‖z.2‖ ≤ blockL2 z.2 := norm_le_blockL2 _
    _ ≤ M*blockL2 z.1 := hz
    _ ≤ M*(Real.sqrt (Fintype.card ι : ℝ)*‖z.1‖) :=
      mul_le_mul_of_nonneg_left (blockL2_le _) hM
    _ = (M*Real.sqrt (Fintype.card ι : ℝ))*‖z.1‖ := by ring

/-- Conversion of a scalar-state bound to the exact Euclidean factor. -/
theorem l2_rate_from_sup {z z0 : BState E} {K r : ℝ} (hK : 0 ≤ K) (hr : 0 ≤ r)
    (h : ‖z‖ ≤ K*r*‖z0‖) :
    stateL2 z ≤ (Real.sqrt (2*(Fintype.card ι : ℝ))*K)*r*stateL2 z0 := by
  calc
    stateL2 z ≤ Real.sqrt (2*(Fintype.card ι : ℝ))*‖z‖ := stateL2_le _
    _ ≤ Real.sqrt (2*(Fintype.card ι : ℝ))*(K*r*‖z0‖) :=
      mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt (2*(Fintype.card ι : ℝ))*(K*r*stateL2 z0) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (norm_le_stateL2 _) (mul_nonneg hK hr)) (Real.sqrt_nonneg _)
    _ = _ := by ring

end BB.Blocks
