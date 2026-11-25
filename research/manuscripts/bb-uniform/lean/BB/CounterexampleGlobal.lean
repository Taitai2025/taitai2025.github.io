import BB.CounterexampleExtension

/-! # Proposition 5.2 with a globally C² objective

The global extension agrees on the full invariant rectangle, preserving every
actual differential, secant, orbit and Euclidean asymptotic conclusion.
-/

noncomputable section
namespace BB.Counterexample
open Set Filter
open scoped Topology

theorem global_c2_counterexample {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    let c := BB.endpointRate a b
    let alpha : ℝ := 2/(a+b)
    let sigma := BB.counterexampleSigma a b
    let G := coordinateGradient a b sigma
    ∃ F : ℝ × ℝ → ℝ, ContDiff ℝ 2 F ∧
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      IsOpen (smallRectangle sigma r) ∧ (0,0) ∈ smallRectangle sigma r ∧
      Convex ℝ (smallRectangle sigma r) ∧
      ContDiffOn ℝ 2 F (smallRectangle sigma r) ∧
      EuclideanStrongConvexOn (smallRectangle sigma r) (a/2) F ∧
      G (0,0) = (0,0) ∧ fderiv ℝ G (0,0) = diagonalMap a b ∧
      (∀ z ∈ smallRectangle sigma r, ∀ w, (fderiv ℝ F z) w = dot2 (G z) w) ∧
      ∀ delta : ℝ, 0 < delta → ∃ r₀ : ℝ,
        let X := orbit c alpha sigma r₀
        0 < norm2 (X 0) ∧ norm2 (X 0) < delta ∧
        (∀ n, X n ∈ smallRectangle sigma r) ∧
        (∀ n, X (n+1) = ((X n).1-alpha*(G (X n)).1, (X n).2-alpha*(G (X n)).2)) ∧
        (∀ n,
          0 < dot2 (pointSecant c alpha sigma r₀ n) (gradientSecant a b c alpha sigma r₀ n) ∧
          0 < normSq2 (gradientSecant a b c alpha sigma r₀ n) ∧
          secantBB2 (pointSecant c alpha sigma r₀ n) (gradientSecant a b c alpha sigma r₀ n) < alpha ∧
          alpha < secantBB1 (pointSecant c alpha sigma r₀ n) (gradientSecant a b c alpha sigma r₀ n)) ∧
        Tendsto (fun n : ℕ => norm2 (X n) ^ (1/(n : ℝ))) atTop (𝓝 c) ∧
        Tendsto (fun n : ℕ => norm2 (G (X n)) ^ (1/(n : ℝ))) atTop (𝓝 c) ∧
        Tendsto (fun n : ℕ => norm2 (X n)/(c^n*norm2 (X 0))) atTop atTop ∧
        Tendsto (fun n : ℕ => norm2 (G (X n))/(c^n*norm2 (G (X 0)))) atTop atTop := by
  dsimp only
  obtain ⟨r,hr,hr1,hopen,hzero,hconv,hc2,hstrong,hGzero,hH,hderiv,horbit⟩ :=
    c2_counterexample ha hab
  obtain ⟨F,hF,heq⟩ := exists_global_c2_extension
    (separableObjective a b (BB.counterexampleSigma a b)) (BB.counterexampleSigma a b)
    (separableObjective_contDiffOn a b (BB.counterexampleSigma a b)) hr hr1
  refine ⟨F,hF,r,hr,hr1,hopen,hzero,hconv,hF.contDiffOn,
    strongConvex_extension heq hstrong,hGzero,hH,?_,horbit⟩
  intro z hz w
  rw [extension_fderiv_eq heq hz]
  exact hderiv z hz w

end BB.Counterexample
