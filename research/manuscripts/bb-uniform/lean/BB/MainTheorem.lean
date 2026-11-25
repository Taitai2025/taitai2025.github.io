import BB.BlockTheorem
import BB.SortedOperator
import BB.OperatorCondition

/-!
# The uniform theorem for actual self-adjoint operators

The state norm below is precisely the Euclidean pair norm in the manuscript.
The spectrum is indexed by distinct eigenvalues, so the displayed prefactor
contains no eigenspace dimensions and no weight-family argument.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Operator

open Module.End

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def pairNorm (z : E × E) : ℝ := Real.sqrt (‖z.1‖^2+‖z.2‖^2)

def stateCone (M : ℝ) (z : E × E) : Prop := ‖z.2‖ ≤ M*‖z.1‖

theorem pairNorm_nonneg (z : E × E) : 0 ≤ pairNorm z := Real.sqrt_nonneg _

theorem norm_le_pairNorm (z : E × E) : ‖z‖ ≤ pairNorm z := by
  rw [Prod.norm_def]
  apply max_le
  · exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ‖z.2‖])
  · exact (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr (by nlinarith [sq_nonneg ‖z.1‖])

theorem pairNorm_le (z : E × E) : pairNorm z ≤ Real.sqrt 2 * ‖z‖ := by
  have h1 : ‖z.1‖ ≤ ‖z‖ := le_max_left _ _
  have h2 : ‖z.2‖ ≤ ‖z‖ := le_max_right _ _
  have hsq1 : ‖z.1‖^2 ≤ ‖z‖^2 := by nlinarith [norm_nonneg z.1, norm_nonneg z]
  have hsq2 : ‖z.2‖^2 ≤ ‖z‖^2 := by nlinarith [norm_nonneg z.2, norm_nonneg z]
  unfold pairNorm
  apply (Real.sqrt_le_iff).mpr
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]

/-- The common function in the original Euclidean pair norm. -/
structure EuclideanCertificate {Ω : Type*} (T : Ω → E × E → E × E) (M c K : ℝ) where
  value : E × E → ℝ
  lipConstant : ℝ
  prefactor_ge_one : 1 ≤ K
  lipConstant_nonneg : 0 ≤ lipConstant
  lower : ∀ z, stateCone M z → pairNorm z ≤ value z
  upper : ∀ z, stateCone M z → value z ≤ K*pairNorm z
  lipschitz : ∀ z z', stateCone M z → stateCone M z' →
    |value z-value z'| ≤ lipConstant*pairNorm (z-z')
  homogeneous : ∀ z, stateCone M z → ∀ t : ℝ, 0 ≤ t → value (t • z) = t*value z
  decrease : ∀ ω z, stateCone M z → value (T ω z) ≤ c*value z

/-- The same function supplies the ordinary product-norm certificate used
in the perturbation argument; only its comparison constants change. -/
def EuclideanCertificate.toSup {Ω : Type*} {T : Ω → E × E → E × E} {M c K : ℝ}
    (v : EuclideanCertificate T M c K) :
    BB.Gluing.Certificate T {z | stateCone M z} c where
  value := v.value
  prefactor := K*Real.sqrt 2
  lipConstant := v.lipConstant*Real.sqrt 2
  prefactor_ge_one := by
    have hs : 1 ≤ Real.sqrt 2 := by
      apply (Real.le_sqrt (by norm_num) (by norm_num)).mpr
      norm_num
    nlinarith [v.prefactor_ge_one]
  lipConstant_nonneg := mul_nonneg v.lipConstant_nonneg (Real.sqrt_nonneg _)
  lower := fun z hz => (norm_le_pairNorm z).trans (v.lower z hz)
  upper := by
    intro z hz
    have h := mul_le_mul_of_nonneg_left (pairNorm_le z)
      ((by norm_num : (0:ℝ) ≤ 1).trans v.prefactor_ge_one)
    exact (v.upper z hz).trans (by nlinarith only [h])
  lipschitz := by
    intro z z' hz hz'
    have h := mul_le_mul_of_nonneg_left (pairNorm_le (z-z')) v.lipConstant_nonneg
    exact (v.lipschitz z z' hz hz').trans (by nlinarith only [h])
  homogeneous := v.homogeneous
  decrease := v.decrease

variable [FiniteDimensional ℝ E]

/-- The first and last entries are bounds for every actual eigenvalue. -/
theorem sorted_spectral_bounds (H : E →ₗ[ℝ] E) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n+2) (μ : Eigenvalues H) :
    sortedLambda H hn 0 ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ sortedLambda H hn (Fin.last (n+1)) := by
  let i := (spectralIndex H hn).symm μ
  have heq : sortedLambda H hn i = (μ:ℝ) := by
    exact congrArg (fun ν : Eigenvalues H => (ν:ℝ)) ((spectralIndex H hn).apply_symm_apply μ)
  rw [← heq]
  exact ⟨(sortedLambda_strictMono H hn).monotone (Fin.zero_le i),
    (sortedLambda_strictMono H hn).monotone (Fin.le_last i)⟩

theorem sortedStateCoordinates_cone {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric) {n : ℕ}
    (hn : Fintype.card (Eigenvalues H) = n) {M : ℝ} (z : E × E) :
    BB.Blocks.l2Cone M (sortedStateCoordinates hH hn z) ↔ stateCone M z := by
  unfold BB.Blocks.l2Cone sortedStateCoordinates stateCone
  rw [sortedCoordinates_norm,sortedCoordinates_norm]

/-- Actual operator version of the common Euclidean Lyapunov theorem.
The energy scale may change arbitrarily with the weight. -/
theorem uniform_operator_certificate {Ω : Type*} {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n+2)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {χ M : ℝ} (hχ : 1 ≤ χ) (hM : 0 ≤ M)
    (W : Ω → E →ₗ[ℝ] E) (hcomm : ∀ ω, Function.Commute H (W ω))
    (m : Ω → ℝ) (hm : ∀ ω, 0 < m ω)
    (hlo : ∀ ω x, m ω*‖x‖^2 ≤ @inner ℝ _ _ x (W ω x))
    (hhi : ∀ ω x, @inner ℝ _ _ x (W ω x) ≤ (χ*m ω)*‖x‖^2) :
    Nonempty (EuclideanCertificate (fun ω => stateMap H (W ω)) M
      (BB.endpointRate (sortedLambda H hn 0) (sortedLambda H hn (Fin.last (n+1))))
      (BB.Blocks.uniformPrefactor (sortedLambda H hn)
        (sortedLambda_strictMono H hn) (sortedLambda_pos hn hpd 0) hχ M)) := by
  obtain ⟨v⟩ := BB.Blocks.uniform_block_certificate (sortedLambda H hn)
    (sortedLambda_strictMono H hn) (sortedLambda_pos hn hpd 0) hχ hM
    (fun ω => sortedEnergy hn (W ω)) m hm
    (fun ω => (sortedEnergy_bounds hn (hlo ω) (hhi ω)).1)
    (fun ω => (sortedEnergy_bounds hn (hlo ω) (hhi ω)).2)
  let coord := sortedStateCoordinates hH hn
  have hc : ∀ z : E × E, stateCone M z → BB.Blocks.l2Cone M (coord z) :=
    fun z hz => (sortedStateCoordinates_cone hH hn z).mpr hz
  have hnorm (z : E × E) : BB.Blocks.stateL2 (coord z) = pairNorm z :=
    sortedStateCoordinates_norm hH hn z
  refine ⟨{
    value := fun z => v.value (coord z)
    lipConstant := v.lipConstant
    prefactor_ge_one := v.prefactor_ge_one
    lipConstant_nonneg := v.lipConstant_nonneg
    lower := ?_
    upper := ?_
    lipschitz := ?_
    homogeneous := ?_
    decrease := ?_
  }⟩
  · intro z hz
    simpa only [hnorm] using v.lower (coord z) (hc z hz)
  · intro z hz
    simpa only [hnorm] using v.upper (coord z) (hc z hz)
  · intro z z' hz hz'
    have hh := v.lipschitz (coord z) (coord z') (hc z hz) (hc z' hz')
    rw [← sortedStateCoordinates_sub hH hn,hnorm] at hh
    exact hh
  · intro z hz t ht
    change v.value (coord (t • z)) = t*v.value (coord z)
    dsimp only [coord]
    rw [sortedStateCoordinates_smul]
    exact v.homogeneous (coord z) (hc z hz) t ht
  · intro ω z hz
    change v.value (coord (stateMap H (W ω) z)) ≤ _
    dsimp only [coord]
    rw [sortedStateMap_conjugacy hH (hcomm ω) hn]
    exact v.decrease ω (coord z) (hc z hz)

/-- Product-norm form, useful when perturbing the actual pair map. -/
theorem uniform_operator_sup_certificate {Ω : Type*} {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n+2)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {χ M : ℝ} (hχ : 1 ≤ χ) (hM : 0 ≤ M)
    (W : Ω → E →ₗ[ℝ] E) (hcomm : ∀ ω, Function.Commute H (W ω))
    (m : Ω → ℝ) (hm : ∀ ω, 0 < m ω)
    (hlo : ∀ ω x, m ω*‖x‖^2 ≤ @inner ℝ _ _ x (W ω x))
    (hhi : ∀ ω x, @inner ℝ _ _ x (W ω x) ≤ (χ*m ω)*‖x‖^2) :
    Nonempty (BB.Gluing.Certificate (fun ω => stateMap H (W ω)) {z | stateCone M z}
      (BB.endpointRate (sortedLambda H hn 0) (sortedLambda H hn (Fin.last (n+1))))) := by
  obtain ⟨v⟩ := uniform_operator_certificate hH hn hpd hχ hM W hcomm m hm hlo hhi
  exact ⟨v.toSup⟩

/-- A uniform bound for every changing sequence of commuting weights,
in exactly the original pair norm and with an explicit spectrum-only prefactor. -/
theorem uniform_operator_rate {Ω : Type*} {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n+2)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {χ M : ℝ} (hχ : 1 ≤ χ) (hM : 0 ≤ M)
    (W : Ω → E →ₗ[ℝ] E) (hcomm : ∀ ω, Function.Commute H (W ω))
    (m : Ω → ℝ) (hm : ∀ ω, 0 < m ω)
    (hlo : ∀ ω x, m ω*‖x‖^2 ≤ @inner ℝ _ _ x (W ω x))
    (hhi : ∀ ω x, @inner ℝ _ _ x (W ω x) ≤ (χ*m ω)*‖x‖^2)
    (w : ℕ → Ω) (z : ℕ → E × E) (hz : stateCone M (z 0))
    (hrec : ∀ k, z (k+1) = stateMap H (W (w k)) (z k)) (k : ℕ) :
    pairNorm (z k) ≤ BB.Blocks.uniformPrefactor (sortedLambda H hn)
      (sortedLambda_strictMono H hn) (sortedLambda_pos hn hpd 0) hχ M *
      (BB.endpointRate (sortedLambda H hn 0) (sortedLambda H hn (Fin.last (n+1))))^k *
      pairNorm (z 0) := by
  have hr : ∀ j, sortedStateCoordinates hH hn (z (j+1)) =
      BB.Blocks.blockMap (sortedLambda H hn) (sortedEnergy hn (W (w j)))
        (sortedStateCoordinates hH hn (z j)) := by
    intro j
    rw [hrec j,sortedStateMap_conjugacy hH (hcomm (w j)) hn]
  have hb := BB.Blocks.uniform_block_rate (sortedLambda H hn)
    (sortedLambda_strictMono H hn) (sortedLambda_pos hn hpd 0) hχ hM
    (fun ω => sortedEnergy hn (W ω)) m hm
    (fun ω => (sortedEnergy_bounds hn (hlo ω) (hhi ω)).1)
    (fun ω => (sortedEnergy_bounds hn (hlo ω) (hhi ω)).2)
    w (fun j => sortedStateCoordinates hH hn (z j))
    ((sortedStateCoordinates_cone hH hn (z 0)).mpr hz) hr k
  simpa only [sortedStateCoordinates_norm,pairNorm] using hb

/-- The manuscript's standard condition-number hypothesis, without any
extra coercivity assumption: each positive scale is obtained from the spectrum. -/
theorem theorem_2_1 {Ω : Type*} {H : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) {n : ℕ} (hn : Fintype.card (Eigenvalues H) = n+2)
    (hpd : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x))
    {χ M : ℝ} (hχ : 1 ≤ χ) (hM : 0 ≤ M)
    (W : Ω → E →ₗ[ℝ] E) [∀ ω, Nonempty (Eigenvalues (W ω))]
    (hW : ∀ ω, (W ω).IsSymmetric)
    (hWpd : ∀ ω x, x ≠ 0 → 0 < @inner ℝ _ _ x (W ω x))
    (hcomm : ∀ ω, Function.Commute H (W ω))
    (hcond : ∀ ω, spectralConditionNumber (W ω) ≤ χ) :
    Nonempty (EuclideanCertificate (fun ω => stateMap H (W ω)) M
      (BB.endpointRate (sortedLambda H hn 0) (sortedLambda H hn (Fin.last (n+1))))
      (BB.Blocks.uniformPrefactor (sortedLambda H hn)
        (sortedLambda_strictMono H hn) (sortedLambda_pos hn hpd 0) hχ M)) ∧
    ∀ (w : ℕ → Ω) (z : ℕ → E × E), stateCone M (z 0) →
      (∀ k, z (k+1) = stateMap H (W (w k)) (z k)) → ∀ k,
      pairNorm (z k) ≤ BB.Blocks.uniformPrefactor (sortedLambda H hn)
        (sortedLambda_strictMono H hn) (sortedLambda_pos hn hpd 0) hχ M *
        (BB.endpointRate (sortedLambda H hn 0) (sortedLambda H hn (Fin.last (n+1))))^k *
        pairNorm (z 0) := by
  have he := fun ω => energy_bounds_of_condition (hW ω) (hWpd ω) (hcond ω)
  choose m hm hbounds using he
  have hlo := fun ω x => (hbounds ω x).1
  have hhi := fun ω x => (hbounds ω x).2
  exact ⟨uniform_operator_certificate hH hn hpd hχ hM W hcomm m hm hlo hhi,
    fun w z hz hr k => uniform_operator_rate hH hn hpd hχ hM W hcomm m hm hlo hhi w z hz hr k⟩

end BB.Operator
