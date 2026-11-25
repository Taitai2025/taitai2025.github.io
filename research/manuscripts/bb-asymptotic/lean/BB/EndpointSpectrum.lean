import BB.TwoPoint
import BB.GradientRates

/-! # Exact sharp endpoint trajectories in an arbitrary finite spectrum -/

namespace BB
noncomputable section
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def pairEmbed (lo hi : ι) (x y : ℝ) (i : ι) : ℝ :=
  if i = lo then x else if i = hi then y else 0

theorem pair_embed_energy (lo hi : ι) (hne : lo ≠ hi) (x y : ℝ) :
    energy (pairEmbed lo hi x y) = x^2 + y^2 := by
  unfold energy
  rw [Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
    (fun i _ hn => by simp [pairEmbed,hn.1,hn.2])]
  simp [pairEmbed,hne,Ne.symm hne]

theorem pair_embed_weighted_energy (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi) (x y : ℝ) :
    (∑ i, lam i * (pairEmbed lo hi x y i)^2) = lam lo*x^2 + lam hi*y^2 := by
  rw [Finset.sum_eq_add_of_mem lo hi (Finset.mem_univ lo) (Finset.mem_univ hi) hne
    (fun i _ hn => by simp [pairEmbed,hn.1,hn.2])]
  simp [pairEmbed,hne,Ne.symm hne]

theorem pair_embed_quotient (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi) (x y : ℝ) :
    diagonalBB1 lam (pairEmbed lo hi x y) = bb1Two (lam lo) (lam hi) x y := by
  unfold diagonalBB1 bb1Two
  rw [pair_embed_energy lo hi hne,pair_embed_weighted_energy lam lo hi hne]

theorem pair_embed_norm (lo hi : ι) (hne : lo ≠ hi) (x y : ℝ) :
    normDiag (pairEmbed lo hi x y) = normTwo x y := by
  unfold normDiag normTwo
  rw [pair_embed_energy lo hi hne]

theorem pair_embed_update (lam : ι → ℝ) (lo hi : ι) (α x y : ℝ) :
    gradientUpdate lam α (pairEmbed lo hi x y) =
      pairEmbed lo hi ((1-α*lam lo)*x) ((1-α*lam hi)*y) := by
  funext i
  by_cases hlo : i = lo
  · simp [gradientUpdate,pairEmbed,hlo]
  · by_cases hhi : i = hi
    · subst i
      simp [gradientUpdate,pairEmbed,hlo]
    · simp [gradientUpdate,pairEmbed,hlo,hhi]

def endpointGradient (lam : ι → ℝ) (lo hi : ι) (x y : ℝ) (n : ℕ) : ι → ℝ :=
  pairEmbed lo hi ((rate (lam lo) (lam hi))^n*x) ((-rate (lam lo) (lam hi))^n*y)

theorem endpoint_gradient_quotient (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (x y : ℝ) (ha : 0 < lam lo) (hab : lam lo < lam hi)
    (hx : x ≠ 0) (hbalance : x^2 = y^2) (n : ℕ) :
    diagonalBB1 lam (endpointGradient lam lo hi x y n) = 2/(lam lo+lam hi) := by
  unfold endpointGradient
  rw [pair_embed_quotient lam lo hi hne]
  exact (exact_endpoint_orbit ha hab hx hbalance n).1

theorem endpoint_gradient_step (lam : ι → ℝ) (lo hi : ι)
    (x y : ℝ) (ha : 0 < lam lo) (hab : lam lo < lam hi) (n : ℕ) :
    gradientUpdate lam (2/(lam lo+lam hi)) (endpointGradient lam lo hi x y n) =
      endpointGradient lam lo hi x y (n+1) := by
  unfold endpointGradient
  rw [pair_embed_update]
  have hs : lam lo+lam hi ≠ 0 := ne_of_gt (by linarith)
  rw [endpoint_left_multiplier hs,endpoint_right_multiplier hs]
  have hl : rate (lam lo) (lam hi) * (rate (lam lo) (lam hi)^n*x) =
      rate (lam lo) (lam hi)^(n+1)*x := by rw [pow_succ]; ring
  have hr : (-rate (lam lo) (lam hi)) * ((-rate (lam lo) (lam hi))^n*y) =
      (-rate (lam lo) (lam hi))^(n+1)*y := by rw [pow_succ]; ring
  rw [hl,hr]

theorem endpoint_gradient_norm (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (x y : ℝ) (ha : 0 < lam lo) (hab : lam lo < lam hi) (n : ℕ) :
    normDiag (endpointGradient lam lo hi x y n) =
      (rate (lam lo) (lam hi))^n * normDiag (endpointGradient lam lo hi x y 0) := by
  simp only [endpointGradient,pair_embed_norm lo hi hne,pow_zero,one_mul]
  exact endpoint_norm_orbit (rate_pos ha hab).le x y n

/-- A fully specified nonzero matched trajectory attains the endpoint factor. -/
theorem endpoint_gradient_is_sharp (lam : ι → ℝ) (lo hi : ι) (hne : lo ≠ hi)
    (x y : ℝ) (ha : 0 < lam lo) (hab : lam lo < lam hi)
    (hx : x ≠ 0) (hbalance : x^2 = y^2) :
    let g := endpointGradient lam lo hi x y
    0 < energy (g 0) ∧
    g 1 = gradientUpdate lam (diagonalBB1 lam (g 0)) (g 0) ∧
    (∀ n, g (n+2) = gradientUpdate lam (diagonalBB1 lam (g n)) (g (n+1))) ∧
    (∀ n, normDiag (g n) = (rate (lam lo) (lam hi))^n * normDiag (g 0)) ∧
    rootFactor (fun n => normDiag (g n) / normDiag (g 0)) = rate (lam lo) (lam hi) := by
  dsimp only
  have he0 : 0 < energy (endpointGradient lam lo hi x y 0) := by
    simp only [endpointGradient,pow_zero,one_mul,pair_embed_energy lo hi hne]
    nlinarith [sq_pos_of_ne_zero hx,sq_nonneg y]
  refine ⟨he0,?_,?_,endpoint_gradient_norm lam lo hi hne x y ha hab,?_⟩
  · rw [endpoint_gradient_quotient lam lo hi hne x y ha hab hx hbalance]
    exact (endpoint_gradient_step lam lo hi x y ha hab 0).symm
  · intro n
    rw [endpoint_gradient_quotient lam lo hi hne x y ha hab hx hbalance]
    exact (endpoint_gradient_step lam lo hi x y ha hab (n+1)).symm
  · have hn0 : normDiag (endpointGradient lam lo hi x y 0) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr he0)
    have hf : (fun n => normDiag (endpointGradient lam lo hi x y n) /
          normDiag (endpointGradient lam lo hi x y 0)) =
        (fun n => (1:ℝ) * (rate (lam lo) (lam hi))^n) := by
      funext n
      rw [endpoint_gradient_norm lam lo hi hne x y ha hab n,mul_div_cancel_right₀ _ hn0,one_mul]
    rw [hf]
    exact rootFactor_geometric 1 _ zero_lt_one (rate_pos ha hab).le

end
end BB
