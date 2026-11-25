import BB.MainTheorem
import BB.OperatorBounds
import BB.WeightedSquareRoot
import BB.RayleighLipschitz

noncomputable section
namespace BB.Operator

open Module.End
open scoped BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual weighted operator quotients lie between the reciprocal spectral endpoints.
No bound on the condition number of W is needed for this interval assertion. -/
theorem weightedAlpha_bounds {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    {u : E} (hu : u ≠ 0) :
    1/b ≤ weightedAlpha H W u ∧ weightedAlpha H W u ≤ 1/a := by
  let e : Eigenvalues H → ℝ := fun μ => ⟪(coordinates hH u μ : E),W (coordinates hH u μ : E)⟫_ℝ
  have he : ∀ μ, 0 ≤ e μ := by
    intro μ
    by_cases hz : (coordinates hH u μ : E)=0
    · simp only [e,hz,inner_zero_left,le_refl]
    · exact (hWpd _ hz).le
  have hnum : 0 < BB.Spectral.numerator (fun _ : Eigenvalues H => 1) e := by
    have hi := hWpd u hu
    rw [mixed_inner_decomposition hH hcomm] at hi
    simpa only [BB.Spectral.numerator,one_mul,e] using hi
  have h := BB.Spectral.alpha_bounds ha hab he (fun _ => (by norm_num : (0:ℝ) ≤ 1))
    (fun μ => (hspec μ).1) (fun μ => (hspec μ).2) hnum
  have hid : weightedAlpha H W u = BB.Spectral.alpha (fun μ : Eigenvalues H => (μ:ℝ))
      (fun _ => 1) e := by
    unfold weightedAlpha BB.Spectral.alpha BB.Spectral.numerator BB.Spectral.denominator
    rw [mixed_inner_decomposition hH hcomm,moment_inner_decomposition hH hcomm]
    simp only [one_mul,e]
  rwa [← hid] at h

theorem weightedAlpha_weightSqrt {H W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W) (u : E) :
    weightedAlpha H W u = BB.Secant.bb1 (weightSqrt hW u) (H (weightSqrt hW u)) := by
  unfold weightedAlpha BB.Secant.bb1
  rw [weightSqrt_commutes hW hcomm u,weightSqrt_inner hW hWpd,
    weightSqrt_sq_norm hW hWpd]

/-- The normalized square-root change of coordinates costs precisely sqrt χ. -/
theorem weightSqrt_unitVector_sub_bound {W : E →ₗ[ℝ] E} (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    {m χ : ℝ} (hm : 0 < m) (hχ : 0 ≤ χ)
    (hq : ∀ x : E, m*‖x‖^2 ≤ ⟪x,W x⟫_ℝ ∧ ⟪x,W x⟫_ℝ ≤ (χ*m)*‖x‖^2)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    ‖unitVector (weightSqrt hW u)-unitVector (weightSqrt hW v)‖ ≤
      (2*Real.sqrt χ)*‖u-v‖/max ‖u‖ ‖v‖ := by
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hmax : 0 < max ‖u‖ ‖v‖ := (norm_pos_iff.mpr hu).trans_le (le_max_left _ _)
  have hlow : Real.sqrt m*max ‖u‖ ‖v‖ ≤ max ‖weightSqrt hW u‖ ‖weightSqrt hW v‖ := by
    rw [mul_max_of_nonneg _ _ hsm.le]
    exact max_le_max (weightSqrt_norm_bounds hW hWpd hm hχ hq u).1
      (weightSqrt_norm_bounds hW hWpd hm hχ hq v).1
  have hdiff : ‖weightSqrt hW u-weightSqrt hW v‖ ≤
      (Real.sqrt χ*Real.sqrt m)*‖u-v‖ := by
    rw [← map_sub]
    exact (weightSqrt_norm_bounds hW hWpd hm hχ hq (u-v)).2
  calc
    _ ≤ 2*‖weightSqrt hW u-weightSqrt hW v‖/max ‖weightSqrt hW u‖ ‖weightSqrt hW v‖ :=
      unitVector_sub_bound (weightSqrt_ne_zero hW hWpd hu) (weightSqrt_ne_zero hW hWpd hv)
    _ ≤ (2*((Real.sqrt χ*Real.sqrt m)*‖u-v‖))/(Real.sqrt m*max ‖u‖ ‖v‖) :=
      div_le_div (by positivity) (mul_le_mul_of_nonneg_left hdiff (by norm_num))
        (mul_pos hsm hmax) hlow
    _ = (2*Real.sqrt χ)*‖u-v‖/max ‖u‖ ‖v‖ := by
      field_simp
      <;> ring

/-- The exact weighted reciprocal-Rayleigh Lipschitz estimate from Lemma 3.2. -/
theorem weightedAlpha_lipschitz_energy {H W : E →ₗ[ℝ] E}
    (hH : H.IsSymmetric) (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W)
    {a b m χ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hm : 0 < m) (hχ : 0 ≤ χ)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hq : ∀ x : E, m*‖x‖^2 ≤ ⟪x,W x⟫_ℝ ∧ ⟪x,W x⟫_ℝ ≤ (χ*m)*‖x‖^2)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    |weightedAlpha H W u-weightedAlpha H W v| ≤
      (2*(b-a)*Real.sqrt χ/a^2)*(‖u-v‖/max ‖u‖ ‖v‖) := by
  rw [weightedAlpha_weightSqrt hW hWpd hcomm,weightedAlpha_weightSqrt hW hWpd hcomm]
  have hrec := reciprocal_rayleigh_unit_bound hH ha hab hspec
    (weightSqrt_ne_zero hW hWpd hu) (weightSqrt_ne_zero hW hWpd hv)
  have hn := weightSqrt_unitVector_sub_bound hW hWpd hm hχ hq hu hv
  calc
    _ ≤ ((b-a)/a^2)*‖unitVector (weightSqrt hW u)-unitVector (weightSqrt hW v)‖ := hrec
    _ ≤ ((b-a)/a^2)*((2*Real.sqrt χ)*‖u-v‖/max ‖u‖ ‖v‖) :=
      mul_le_mul_of_nonneg_left hn (div_nonneg (sub_nonneg.mpr hab) (sq_nonneg a))
    _ = (2*(b-a)*Real.sqrt χ/a^2)*(‖u-v‖/max ‖u‖ ‖v‖) := by ring

theorem weightedAlpha_lipschitz {H W : E →ₗ[ℝ] E} [Nonempty (Eigenvalues W)]
    (hH : H.IsSymmetric) (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W)
    {a b χ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hcond : spectralConditionNumber W ≤ χ)
    {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    |weightedAlpha H W u-weightedAlpha H W v| ≤
      (2*(b-a)*Real.sqrt χ/a^2)*(‖u-v‖/max ‖u‖ ‖v‖) := by
  obtain ⟨m,hm,hq⟩ := energy_bounds_of_condition hW hWpd hcond
  exact weightedAlpha_lipschitz_energy hH hW hWpd hcomm ha hab hm hχ hspec hq hu hv

def growthConstant (a b : ℝ) : ℝ := Real.sqrt (1+(b/a-1)^2)

def operatorLipConstant (a b M χ : ℝ) : ℝ :=
  b/a+2*(b/a)*(b/a-1)*M*Real.sqrt χ

theorem pairNorm_sq (z : E × E) : (pairNorm z)^2=‖z.1‖^2+‖z.2‖^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem pairNorm_le_sum (z : E × E) : pairNorm z ≤ ‖z.1‖+‖z.2‖ := by
  unfold pairNorm
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact add_nonneg (norm_nonneg _) (norm_nonneg _)
  · nlinarith only [mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]

theorem pairNorm_sub_comm (z z' : E × E) : pairNorm (z-z')=pairNorm (z'-z) := by
  simp only [pairNorm,Prod.fst_sub,Prod.snd_sub,norm_sub_rev]

theorem stateCone_zero_of_fst_zero {M : ℝ} {z : E × E}
    (hz : stateCone M z) (hu : z.1=0) : z=0 := by
  have hv : z.2=0 := by
    apply norm_eq_zero.mp
    have hh := hz
    change ‖z.2‖ ≤ M*‖z.1‖ at hh
    rw [hu,norm_zero,mul_zero] at hh
    exact le_antisymm hh (norm_nonneg _)
  exact Prod.ext hu hv

theorem stateMap_zero (H W : E →ₗ[ℝ] E) : stateMap H W 0=0 := by
  simp [stateMap]

theorem growthConstant_le_ratio {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    growthConstant a b ≤ b/a := by
  have hκ : 1 ≤ b/a := (one_le_div ha).mpr hab
  unfold growthConstant
  apply Real.sqrt_le_iff.mpr
  exact ⟨by linarith only [hκ],by nlinarith only [hκ]⟩

theorem ratio_le_operatorLipConstant {a b M χ : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hM : 0 ≤ M) : b/a ≤ operatorLipConstant a b M χ := by
  have hκ : 1 ≤ b/a := (one_le_div ha).mpr hab
  have hd : 0 ≤ b/a-1 := by linarith only [hκ]
  unfold operatorLipConstant
  have hh : 0 ≤ 2*(b/a)*(b/a-1)*M*Real.sqrt χ := by positivity
  linarith only [hh]

/-- The exact Euclidean one-step growth constant B in the manuscript. -/
theorem stateMap_growth {H W : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (hcomm : Function.Commute H W)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    {a b M : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (z : E × E) (hz : stateCone M z) :
    pairNorm (stateMap H W z) ≤ growthConstant a b*pairNorm z := by
  by_cases hu : z.1=0
  · have hzero := stateCone_zero_of_fst_zero hz hu
    simp [hzero,stateMap_zero,pairNorm]
  have hα := weightedAlpha_bounds hH hcomm hWpd ha hab hspec hu
  have hg := spectral_step_norm_bound hH ha hab hspec hα.1 hα.2 z.2
  have hκ : 1 ≤ b/a := (one_le_div ha).mpr hab
  have hd : 0 ≤ b/a-1 := by linarith only [hκ]
  have hs : ‖z.2-weightedAlpha H W z.1 • H z.2‖^2 ≤ (b/a-1)^2*‖z.2‖^2 := by
    have hh := mul_self_le_mul_self (norm_nonneg _) hg
    nlinarith only [hh]
  have hB : (growthConstant a b)^2=1+(b/a-1)^2 :=
    Real.sq_sqrt (by positivity)
  have hv : ‖z.2‖ ≤ pairNorm z := (le_max_right _ _).trans (norm_le_pairNorm z)
  have hv2 : ‖z.2‖^2 ≤ (pairNorm z)^2 := by
    nlinarith only [hv,norm_nonneg z.2,pairNorm_nonneg z]
  have hsq : (pairNorm (stateMap H W z))^2 ≤ (growthConstant a b*pairNorm z)^2 := by
    rw [pairNorm_sq,mul_pow,hB]
    change ‖z.2‖^2+‖z.2-weightedAlpha H W z.1 • H z.2‖^2 ≤
      (1+(b/a-1)^2)*(pairNorm z)^2
    have hh := mul_le_mul_of_nonneg_left hv2 (by positivity : 0 ≤ 1+(b/a-1)^2)
    nlinarith only [hh,hs]
  have hn : 0 ≤ growthConstant a b*pairNorm z :=
    mul_nonneg (Real.sqrt_nonneg _) (pairNorm_nonneg z)
  nlinarith only [hsq,hn,pairNorm_nonneg (stateMap H W z)]

/-- Difference estimate for the second state component, ordered by previous-gradient norm. -/
theorem stateMap_second_difference_ordered {H W : E →ₗ[ℝ] E} [Nonempty (Eigenvalues W)]
    (hH : H.IsSymmetric) (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W)
    {a b M χ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hχ : 0 ≤ χ)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hcond : spectralConditionNumber W ≤ χ)
    {u v u' v' : E} (hu : u ≠ 0) (hu' : u' ≠ 0)
    (hcone : ‖v‖ ≤ M*‖u‖) (horder : ‖u'‖ ≤ ‖u‖) :
    ‖(v-weightedAlpha H W u • H v)-(v'-weightedAlpha H W u' • H v')‖ ≤
      (b/a-1)*‖v-v'‖+(2*(b/a)*(b/a-1)*M*Real.sqrt χ)*‖u-u'‖ := by
  have hnu : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hb : 0 ≤ b := (ha.trans_le hab).le
  let C : ℝ := 2*(b-a)*Real.sqrt χ/a^2
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
      (Real.sqrt_nonneg _)) (sq_nonneg _)
  have hα : |weightedAlpha H W u-weightedAlpha H W u'| ≤ C*(‖u-u'‖/‖u‖) := by
    simpa only [max_eq_left horder] using
      weightedAlpha_lipschitz hH hW hWpd hcomm ha hab hχ hspec hcond hu hu'
  have hHv : ‖H v‖ ≤ (b*M)*‖u‖ := by
    calc
      _ ≤ b*‖v‖ := (positive_spectral_bounds hH ha hab hspec v).2
      _ ≤ b*(M*‖u‖) := mul_le_mul_of_nonneg_left hcone hb
      _ = (b*M)*‖u‖ := by ring
  have hprod : |weightedAlpha H W u-weightedAlpha H W u'| * ‖H v‖ ≤
      (2*(b/a)*(b/a-1)*M*Real.sqrt χ)*‖u-u'‖ := by
    calc
      _ ≤ (C*(‖u-u'‖/‖u‖))*((b*M)*‖u‖) :=
        mul_le_mul hα hHv (norm_nonneg _) (mul_nonneg hC (div_nonneg (norm_nonneg _) hnu.le))
      _ = (2*(b/a)*(b/a-1)*M*Real.sqrt χ)*‖u-u'‖ := by
        dsimp only [C]
        field_simp
        <;> ring
  have hβ := weightedAlpha_bounds hH hcomm hWpd ha hab hspec hu'
  have hid : (v-weightedAlpha H W u • H v)-(v'-weightedAlpha H W u' • H v') =
      ((v-v')-weightedAlpha H W u' • H (v-v'))+
        (weightedAlpha H W u'-weightedAlpha H W u) • H v := by
    rw [map_sub,smul_sub,sub_smul]
    abel
  rw [hid]
  calc
    _ ≤ ‖(v-v')-weightedAlpha H W u' • H (v-v')‖+
        ‖(weightedAlpha H W u'-weightedAlpha H W u) • H v‖ := norm_add_le _ _
    _ = ‖(v-v')-weightedAlpha H W u' • H (v-v')‖+
        |weightedAlpha H W u-weightedAlpha H W u'| * ‖H v‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_sub_comm]
    _ ≤ (b/a-1)*‖v-v'‖+(2*(b/a)*(b/a-1)*M*Real.sqrt χ)*‖u-u'‖ :=
      add_le_add (spectral_step_norm_bound hH ha hab hspec hβ.1 hβ.2 (v-v')) hprod

theorem stateMap_lipschitz_ordered {H W : E →ₗ[ℝ] E} [Nonempty (Eigenvalues W)]
    (hH : H.IsSymmetric) (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W)
    {a b M χ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hχ : 0 ≤ χ)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hcond : spectralConditionNumber W ≤ χ)
    {z z' : E × E} (hu : z.1 ≠ 0) (hu' : z'.1 ≠ 0)
    (hz : stateCone M z) (horder : ‖z'.1‖ ≤ ‖z.1‖) :
    pairNorm (stateMap H W z-stateMap H W z') ≤
      operatorLipConstant a b M χ*pairNorm (z-z') := by
  let A : ℝ := 2*(b/a)*(b/a-1)*M*Real.sqrt χ
  have hκ : 1 ≤ b/a := (one_le_div ha).mpr hab
  have hκ0 : 0 ≤ b/a := by linarith only [hκ]
  have hd : 0 ≤ b/a-1 := by linarith only [hκ]
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hsecond := stateMap_second_difference_ordered (v' := z'.2) hH hW hWpd hcomm ha hab hM hχ
    hspec hcond hu hu' hz horder
  have huD : ‖z.1-z'.1‖ ≤ pairNorm (z-z') :=
    (le_max_left _ _).trans (norm_le_pairNorm (z-z'))
  have hvD : ‖z.2-z'.2‖ ≤ pairNorm (z-z') :=
    (le_max_right _ _).trans (norm_le_pairNorm (z-z'))
  calc
    _ ≤ ‖z.2-z'.2‖+
        ‖(z.2-weightedAlpha H W z.1 • H z.2)-(z'.2-weightedAlpha H W z'.1 • H z'.2)‖ :=
      pairNorm_le_sum (stateMap H W z-stateMap H W z')
    _ ≤ ‖z.2-z'.2‖+((b/a-1)*‖z.2-z'.2‖+A*‖z.1-z'.1‖) :=
      add_le_add_left hsecond _
    _ = (b/a)*‖z.2-z'.2‖+A*‖z.1-z'.1‖ := by ring
    _ ≤ (b/a)*pairNorm (z-z')+A*pairNorm (z-z') :=
      add_le_add (mul_le_mul_of_nonneg_left hvD hκ0) (mul_le_mul_of_nonneg_left huD hA)
    _ = operatorLipConstant a b M χ*pairNorm (z-z') := by
      unfold operatorLipConstant
      dsimp only [A]
      ring

/-- The exact global Euclidean cone Lipschitz constant L from Lemma 3.2,
including both zero-state boundary cases. -/
theorem stateMap_lipschitz {H W : E →ₗ[ℝ] E} [Nonempty (Eigenvalues W)]
    (hH : H.IsSymmetric) (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W)
    {a b M χ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hχ : 0 ≤ χ)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hcond : spectralConditionNumber W ≤ χ)
    (z z' : E × E) (hz : stateCone M z) (hz' : stateCone M z') :
    pairNorm (stateMap H W z-stateMap H W z') ≤
      operatorLipConstant a b M χ*pairNorm (z-z') := by
  have hBL : growthConstant a b ≤ operatorLipConstant a b M χ :=
    (growthConstant_le_ratio ha hab).trans (ratio_le_operatorLipConstant ha hab hM)
  have hzero_right (y : E × E) (hy : stateCone M y) :
      pairNorm (stateMap H W y-stateMap H W 0) ≤
        operatorLipConstant a b M χ*pairNorm (y-0) := by
    rw [stateMap_zero,sub_zero,sub_zero]
    exact (stateMap_growth hH hcomm hWpd ha hab hspec y hy).trans
      (mul_le_mul_of_nonneg_right hBL (pairNorm_nonneg y))
  by_cases hu : z.1=0
  · have hz0 := stateCone_zero_of_fst_zero hz hu
    rw [hz0,pairNorm_sub_comm (stateMap H W 0) (stateMap H W z'),pairNorm_sub_comm 0 z']
    exact hzero_right z' hz'
  by_cases hu' : z'.1=0
  · have hz'0 := stateCone_zero_of_fst_zero hz' hu'
    rw [hz'0]
    exact hzero_right z hz
  rcases le_total ‖z'.1‖ ‖z.1‖ with ho|ho
  · exact stateMap_lipschitz_ordered hH hW hWpd hcomm ha hab hM hχ hspec hcond hu hu' hz ho
  · calc
      _ = pairNorm (stateMap H W z'-stateMap H W z) := pairNorm_sub_comm _ _
      _ ≤ operatorLipConstant a b M χ*pairNorm (z'-z) :=
        stateMap_lipschitz_ordered hH hW hWpd hcomm ha hab hM hχ hspec hcond hu' hu hz' ho
      _ = operatorLipConstant a b M χ*pairNorm (z-z') := by rw [pairNorm_sub_comm z' z]

/-- Full displayed Lemma 3.2, with the manuscript's B and L rather than enlarged constants. -/
theorem lemma_3_2 {H W : E →ₗ[ℝ] E} [Nonempty (Eigenvalues W)]
    (hH : H.IsSymmetric) (hW : W.IsSymmetric)
    (hWpd : ∀ x : E, x ≠ 0 → 0 < ⟪x,W x⟫_ℝ)
    (hcomm : Function.Commute H W)
    {a b M χ : ℝ} (ha : 0 < a) (hab : a ≤ b) (hM : 0 ≤ M) (hχ : 0 ≤ χ)
    (hspec : ∀ μ : Eigenvalues H, a ≤ (μ:ℝ) ∧ (μ:ℝ) ≤ b)
    (hcond : spectralConditionNumber W ≤ χ) :
    (∀ z : E × E, stateCone M z →
      pairNorm (stateMap H W z) ≤ Real.sqrt (1+(b/a-1)^2)*pairNorm z) ∧
    (∀ z z' : E × E, stateCone M z → stateCone M z' →
      pairNorm (stateMap H W z-stateMap H W z') ≤
        (b/a+2*(b/a)*(b/a-1)*M*Real.sqrt χ)*pairNorm (z-z')) :=
  ⟨stateMap_growth hH hcomm hWpd ha hab hspec,
    stateMap_lipschitz hH hW hWpd hcomm ha hab hM hχ hspec hcond⟩

end BB.Operator
