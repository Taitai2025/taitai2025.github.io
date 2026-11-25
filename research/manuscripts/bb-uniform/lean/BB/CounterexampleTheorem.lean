import BB.CounterexampleNorms
import BB.Dini

/-!
# The local C² counterexample, assembled

The objective, genuine differential, Hessian, strong convexity, actual iteration,
true secants, and Euclidean norm limits are all connected in `c2_counterexample`.
The objective is C² on an explicit open neighborhood, matching the local
construction used in the manuscript.
-/

namespace BB.Counterexample

noncomputable section
set_option maxHeartbeats 500000
open scoped Topology BigOperators
open Filter Set MeasureTheory

theorem smallRectangle_isOpen (sigma r : ℝ) : IsOpen (smallRectangle sigma r) := by
  exact (isOpen_lt (continuous_abs.comp continuous_fst) continuous_const).inter
    (isOpen_lt (continuous_abs.comp (continuous_snd.div_const sigma)) continuous_const)

theorem smallRectangle_zero {sigma r : ℝ} (hr : 0 < r) :
    (0,0) ∈ smallRectangle sigma r := by simp [smallRectangle, hr]

theorem smallRectangle_subset {sigma r : ℝ} (hr : r ≤ 1) :
    smallRectangle sigma r ⊆ constructionDomain sigma := by
  intro z hz
  exact ⟨abs_lt.mp (hz.1.trans_le hr), abs_lt.mp (hz.2.trans_le hr)⟩

theorem smallRectangle_convex (sigma r : ℝ) : Convex ℝ (smallRectangle sigma r) := by
  intro x hx y hy t u ht hu hsum
  constructor
  · change |t*x.1 + u*y.1| < r
    apply abs_lt.mpr
    exact (convex_Ioo (-r) r) (abs_lt.mp hx.1) (abs_lt.mp hy.1) ht hu hsum
  · change |(t*x.2 + u*y.2)/sigma| < r
    have heq : (t*x.2 + u*y.2)/sigma = t*(x.2/sigma) + u*(y.2/sigma) := by ring
    rw [heq]
    apply abs_lt.mpr
    exact (convex_Ioo (-r) r) (abs_lt.mp hx.2) (abs_lt.mp hy.2) ht hu hsum

theorem orbit_mem_smallRectangle {c alpha sigma r₀ gamma r : ℝ}
    (hc : 0 < c) (halpha : 0 ≤ alpha) (hsigma : sigma ≠ 0)
    (hr₀ : 0 < r₀) (hr₁ : r₀ < 1) (hgamma : gamma < 1)
    (hsmall : c + alpha * logModulus r₀ ≤ gamma) (hrr : r₀ < r) (n : ℕ) :
    orbit c alpha sigma r₀ n ∈ smallRectangle sigma r := by
  have hInv := radius_invariant hc halpha hr₀ hr₁ hgamma hsmall n
  constructor
  · simpa only [orbit, abs_of_pos hInv.1] using hInv.2.trans_lt hrr
  · change |((-1 : ℝ)^n * sigma * radius c alpha r₀ n) / sigma| < r
    have heq : ((-1 : ℝ)^n * sigma * radius c alpha r₀ n) / sigma =
        (-1 : ℝ)^n * radius c alpha r₀ n := by field_simp; ring
    rw [heq, abs_mul, abs_pow]
    simpa [abs_of_pos hInv.1] using hInv.2.trans_lt hrr

/-- Full local version of Proposition 5.2, with all analytic and algorithmic
claims connected to one explicit objective. -/
theorem c2_counterexample {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    let c := BB.endpointRate a b
    let alpha : ℝ := 2/(a+b)
    let sigma := BB.counterexampleSigma a b
    let F := separableObjective a b sigma
    let G := coordinateGradient a b sigma
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
  let c := BB.endpointRate a b
  let alpha : ℝ := 2/(a+b)
  let sigma := BB.counterexampleSigma a b
  have hb : 0 < b := ha.trans hab
  have hsigma : 0 < sigma := (BB.counterexampleSigma_conditions ha hab).1
  have hc : 0 < c := BB.endpointRate_pos ha hab
  have hc₁ : c < 1 := BB.endpointRate_lt_one ha hab
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  obtain ⟨r, hr, hr₁, hd⟩ := exists_small_hessian_radius ha
  refine ⟨r, hr, hr₁, smallRectangle_isOpen sigma r, smallRectangle_zero hr,
    smallRectangle_convex sigma r, (separableObjective_contDiffOn a b sigma).mono
      (smallRectangle_subset hr₁.le),
    separableObjective_strongConvex ha hab.le hsigma.ne' hr₁.le
      (fun x hx => ⟨(hd x hx).1, (hd x hx).2.le⟩),
    coordinateGradient_zero a b sigma, coordinateGradient_derivative_zero a b hsigma.ne',
    ?_, ?_⟩
  · intro z hz w
    exact objective_differential a b hsigma.ne' (smallRectangle_subset hr₁.le hz) w
  · intro delta hdelta
    have hC : 0 < Real.sqrt (1+sigma^2) := Real.sqrt_pos.mpr (by nlinarith [sq_nonneg sigma])
    obtain ⟨r₀, hr₀, hrmin, hr₀₁, hsmall, _, _, hsecant⟩ :=
      arbitrarily_small_admissible_orbits ha hab (min r (delta/Real.sqrt (1+sigma^2)))
        (lt_min hr (div_pos hdelta hC))
    have hrr : r₀ < r := hrmin.trans_le (min_le_left _ _)
    have hrδ : r₀ < delta/Real.sqrt (1+sigma^2) := hrmin.trans_le (min_le_right _ _)
    let gamma : ℝ := (c+1)/2
    have hγ₀ : 0 < gamma := by dsimp [gamma]; positivity
    have hγ₁ : gamma < 1 := by dsimp [gamma]; linarith only [hc₁]
    have hs : c + alpha*logModulus r₀ ≤ gamma := hsmall
    have hInv := radius_invariant hc halpha.le hr₀ hr₀₁ hγ₁ hs
    have hnorm₀ : norm2 (orbit c alpha sigma r₀ 0) = r₀*Real.sqrt (1+sigma^2) := by
      simpa using norm2_orbit (sigma := sigma) (hInv 0).1.le
    have hgrad₀ : 0 < norm2 (previousNormalized a b sigma r₀) := by
      have hder := (hd r₀ (by simpa [abs_of_pos hr₀] using hrr)).2
      have hfirst : 0 < a-logModulus r₀ := by
        dsimp [modulusDerivative] at hder
        nlinarith only [hder, ha, sq_nonneg (logModulus r₀)]
      apply Real.sqrt_pos.mpr
      dsimp [norm2, normSq2, dot2, previousNormalized]
      nlinarith only [sq_pos_of_pos hfirst, sq_nonneg (sigma*(b+logModulus r₀))]
    have hrel₁ : 1-alpha*a=c := by
      dsimp [alpha, c, BB.endpointRate]
      field_simp [(add_pos ha hb).ne', (add_pos hb ha).ne']
      <;> ring
    have hrel₂ : 1-alpha*b= -c := by
      dsimp [alpha, c, BB.endpointRate]
      field_simp [(add_pos ha hb).ne', (add_pos hb ha).ne']
      <;> ring
    refine ⟨r₀, ?_, ?_, ?_, ?_, hsecant, ?_, ?_, ?_, ?_⟩
    · rw [hnorm₀]
      exact mul_pos hr₀ hC
    · rw [hnorm₀]
      exact (lt_div_iff hC).mp hrδ
    · exact orbit_mem_smallRectangle hc halpha.le hsigma.ne' hr₀ hr₀₁ hγ₁ hs hrr
    · exact orbit_step a b c alpha r₀ hsigma.ne' hrel₁ hrel₂
    · exact orbit_norm_root_limit hc halpha.le hr₀ hr₀₁ hγ₀.le hγ₁ hs
    · exact gradient_norm_root_limit ha hsigma.ne' hc halpha.le hr₀ hr₀₁ hγ₀.le hγ₁ hs
    · exact orbit_norm_normalized_diverges hc hc₁ halpha hr₀ hr₀₁ hγ₁ hs
    · exact gradient_norm_normalized_diverges ha hsigma.ne' hc hc₁ halpha hr₀ hr₀₁ hγ₀.le hγ₁ hs hgrad₀

end
end BB.Counterexample
