import BB.TwoPoint
import BB.Asymptotics

/-! # The complete positive projective recurrence and its logarithmic growth -/

namespace BB
noncomputable section

theorem positive_ratio_log_recurrence (z : ℕ → ℝ)
    (hz : ∀ n, 0 < z n)
    (hrec : ∀ n, z (n+2) = z (n+1) / z n ^ 2) :
    ∀ n, Real.log (z (n+2)) = Real.log (z (n+1)) - 2 * Real.log (z n) := by
  intro n
  exact log_ratio_recurrence (hz (n+1)) (hz n) (hrec n)

theorem matched_log_initial_value {z : ℕ → ℝ} (hmatched : z 1 = (z 0)⁻¹) :
    Real.log (z 1) = -Real.log (z 0) := by
  rw [hmatched, Real.log_inv]

theorem positive_ratio_log_growth (z : ℕ → ℝ)
    (hz : ∀ n, 0 < z n)
    (hrec : ∀ n, z (n+2) = z (n+1) / z n ^ 2)
    (hne : z 0 ≠ 1 ∨ z 1 ≠ 1) :
    rootFactor (fun n => |Real.log (z n)|) = Real.sqrt 2 := by
  apply recurrence_rootFactor_abs (fun n => Real.log (z n))
    (positive_ratio_log_recurrence z hz hrec)
  intro hzero
  have h0 : z 0 = 1 := by
    have hh := congrArg Real.exp hzero.1
    simpa only [Real.exp_log (hz 0), Real.exp_zero] using hh
  have h1 : z 1 = 1 := by
    have hh := congrArg Real.exp hzero.2
    simpa only [Real.exp_log (hz 1), Real.exp_zero] using hh
  rcases hne with h | h
  · exact h h0
  · exact h h1

theorem positive_ratio_compact_iff (z : ℕ → ℝ)
    (hz : ∀ n, 0 < z n)
    (hrec : ∀ n, z (n+2) = z (n+1) / z n ^ 2) :
    (∃ l u : ℝ, 0 < l ∧ ∀ n, l ≤ z n ∧ z n ≤ u) ↔ ∀ n, z n = 1 := by
  constructor
  · rintro ⟨l,u,hl,hlub⟩
    have hlogs : ∀ n, |Real.log (z n)| ≤ |Real.log l| + |Real.log u| := by
      intro n
      have hlow := Real.log_le_log hl (hlub n).1
      have hupp := Real.log_le_log (hz n) (hlub n).2
      apply abs_le.mpr
      constructor
      · linarith [neg_abs_le (Real.log l), abs_nonneg (Real.log u)]
      · linarith [le_abs_self (Real.log u), abs_nonneg (Real.log l)]
    have hinit := recurrence_bounded_initial_zero (fun n => Real.log (z n))
      (positive_ratio_log_recurrence z hz hrec) _ hlogs
    have hall := recurrence_zero_of_initial_zero (fun n => Real.log (z n))
      (positive_ratio_log_recurrence z hz hrec) hinit.1 hinit.2
    intro n
    have hh := congrArg Real.exp (hall n)
    simpa only [Real.exp_log (hz n), Real.exp_zero] using hh
  · intro hall
    refine ⟨1,1,zero_lt_one,?_⟩
    intro n
    rw [hall n]
    exact ⟨le_rfl,le_rfl⟩

/-- The nonlinear projective recurrence is derived from actual real BB1 updates,
not included as a conclusion-shaped hypothesis. -/
theorem bb1_two_orbit_ratio_recurrence {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx : ∀ n, x n ≠ 0) (hy : ∀ n, y n ≠ 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1)) :
    ∀ n, ratioTwo (x (n+2)) (y (n+2)) =
      ratioTwo (x (n+1)) (y (n+1)) / (ratioTwo (x n) (y n))^2 := by
  intro n
  rw [hxu n,hyu n]
  exact two_point_ratio_recurrence ha hab (hx n) (hy n) (hy (n+1))

theorem bb1_two_orbit_log_growth {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (x y : ℕ → ℝ) (hx : ∀ n, x n ≠ 0) (hy : ∀ n, y n ≠ 0)
    (hxu : ∀ n, x (n+2) = (1-bb1Two a b (x n) (y n)*a)*x (n+1))
    (hyu : ∀ n, y (n+2) = (1-bb1Two a b (x n) (y n)*b)*y (n+1))
    (hne : ratioTwo (x 0) (y 0) ≠ 1) :
    rootFactor (fun n => |Real.log (ratioTwo (x n) (y n))|) = Real.sqrt 2 := by
  apply positive_ratio_log_growth (fun n => ratioTwo (x n) (y n))
  · intro n
    exact div_pos (sq_pos_of_ne_zero (hx n)) (sq_pos_of_ne_zero (hy n))
  · exact bb1_two_orbit_ratio_recurrence ha hab x y hx hy hxu hyu
  · exact Or.inl hne

end
end BB
