import BB.DefectTrajectory
import BB.OperatorEndpointSupport
import BB.OperatorBridge
import BB.BaselineNormalized

/-! # Exact endpoint dissipation for actual changing-weight operator trajectories

The scalar endpoint-size trajectory is constructed from the actual orthogonal
spectral coordinates of the current gradient.  Its recurrence, interior
reciprocal steps, and positivity are consequences of the operator update and
endpoint persistence. No scalar energy law is supplied as an assumption.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Operator
open Module.End Set Filter
open scoped Topology BigOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Data of an actual delayed operator-gradient orbit. The pair stores the
previous and current gradients. The two specified eigenvalues are its spectral
endpoints, and both endpoint components are present in the initial pair. -/
structure EndpointOperatorOrbit {H : E →ₗ[ℝ] E} (hH : H.IsSymmetric)
    (lo hi : Eigenvalues H) where
  weight : ℕ → E →ₗ[ℝ] E
  state : ℕ → E × E
  commutes : ∀ n, Function.Commute H (weight n)
  weight_positive : ∀ n, ∀ v : E, v ≠ 0 → 0 < @inner ℝ _ _ v (weight n v)
  lower_positive : 0 < (lo : ℝ)
  endpoints_distinct : (lo : ℝ) < (hi : ℝ)
  initial_supported : intervalStateSupported hH lo hi (state 0)
  initial_present : endpointStatePresent hH lo hi (state 0)
  step : ∀ n, state (n+1)=stateMap H (weight n) (state n)

namespace EndpointOperatorOrbit
variable {H : E →ₗ[ℝ] E} {hH : H.IsSymmetric} {lo hi : Eigenvalues H}
  (O : EndpointOperatorOrbit hH lo hi)

/-- Direct constructor when the stated endpoints are the global spectral endpoints.
The general orbit structure also permits strictly smaller active spectral faces. -/
def ofGlobalSpectrum
    (W : ℕ → E →ₗ[ℝ] E) (z : ℕ → E × E)
    (hcomm : ∀ n, Function.Commute H (W n))
    (hW : ∀ n, ∀ v : E, v ≠ 0 → 0 < @inner ℝ _ _ v (W n v))
    (ha : 0 < (lo : ℝ)) (hab : (lo : ℝ) < (hi : ℝ))
    (hspec : ∀ mu : Eigenvalues H, (lo : ℝ) ≤ (mu : ℝ) ∧ (mu : ℝ) ≤ (hi : ℝ))
    (hz : endpointStatePresent hH lo hi (z 0))
    (hstep : ∀ n, z (n+1)=stateMap H (W n) (z n)) : EndpointOperatorOrbit hH lo hi where
  weight := W
  state := z
  commutes := hcomm
  weight_positive := hW
  lower_positive := ha
  endpoints_distinct := hab
  initial_supported := ⟨intervalSupported_of_global_bounds hH hspec _,
    intervalSupported_of_global_bounds hH hspec _⟩
  initial_present := hz
  step := hstep

/-- Reciprocal quotient formed from the actual previous gradient. -/
def tau (n : ℕ) : ℝ := weightedTau H (O.weight n) (O.state n).1

def lowSize (n : ℕ) : ℝ := ‖coordinates hH (O.state n).2 lo‖
def highSize (n : ℕ) : ℝ := ‖coordinates hH (O.state n).2 hi‖

theorem tau_eq_reciprocal (n : ℕ) :
    O.tau n=1/weightedAlpha H (O.weight n) (O.state n).1 :=
  weightedTau_eq H (O.weight n) (O.state n).1

theorem interval_supported (n : ℕ) : intervalStateSupported hH lo hi (O.state n) :=
  trajectory_interval_supported hH O.weight O.state O.initial_supported O.step n

theorem endpoints_present (n : ℕ) : endpointStatePresent hH lo hi (O.state n) :=
  endpoint_state_persistence_on_support hH O.weight O.commutes O.weight_positive O.lower_positive
    O.endpoints_distinct O.state O.initial_supported O.initial_present O.step n

theorem tau_interior (n : ℕ) : (lo : ℝ) < O.tau n ∧ O.tau n < (hi : ℝ) :=
  weightedTau_strict_bounds_on_support hH (O.commutes n) (O.weight_positive n) O.lower_positive
    O.endpoints_distinct (O.interval_supported n).1 (O.endpoints_present n).1

theorem alpha_interior (n : ℕ) :
    1/(hi : ℝ) < weightedAlpha H (O.weight n) (O.state n).1 ∧
      weightedAlpha H (O.weight n) (O.state n).1 < 1/(lo : ℝ) :=
  weightedAlpha_strict_bounds_on_support hH (O.commutes n) (O.weight_positive n) O.lower_positive
    O.endpoints_distinct (O.interval_supported n).1 (O.endpoints_present n).1

theorem alpha_positive (n : ℕ) : 0 < weightedAlpha H (O.weight n) (O.state n).1 :=
  (one_div_pos.mpr (O.lower_positive.trans O.endpoints_distinct)).trans (O.alpha_interior n).1

theorem lowSize_positive (n : ℕ) : 0 < O.lowSize n :=
  norm_pos_iff.mpr (O.endpoints_present n).2.1

theorem highSize_positive (n : ℕ) : 0 < O.highSize n :=
  norm_pos_iff.mpr (O.endpoints_present n).2.2

/-- Actual spectral projection norm update, prior to using endpoint signs. -/
theorem coordinate_norm_step (mu : Eigenvalues H) (n : ℕ) :
    ‖coordinates hH (O.state (n+1)).2 mu‖ =
      |1-weightedAlpha H (O.weight n) (O.state n).1*(mu : ℝ)| *
        ‖coordinates hH (O.state n).2 mu‖ := by
  rw [O.step n]
  change ‖coordinates hH ((O.state n).2-
    weightedAlpha H (O.weight n) (O.state n).1 • H (O.state n).2) mu‖ = _
  rw [coordinates_step,norm_smul,Real.norm_eq_abs]

/-- The lower endpoint-size recurrence follows from the genuine operator update. -/
theorem lowSize_step (n : ℕ) :
    O.lowSize (n+1)=((O.tau n-(lo : ℝ))/O.tau n)*O.lowSize n := by
  have ha := O.lower_positive
  have hα := O.alpha_positive n
  have hbound := (lt_div_iff ha).mp (O.alpha_interior n).2
  change ‖coordinates hH (O.state (n+1)).2 lo‖ = _
  rw [O.coordinate_norm_step lo n,abs_of_nonneg (by linarith only [hbound])]
  have hid : 1-weightedAlpha H (O.weight n) (O.state n).1*(lo : ℝ) =
      (O.tau n-(lo : ℝ))/O.tau n := by
    rw [O.tau_eq_reciprocal]
    field_simp [hα.ne'] <;> ring
  rw [hid]
  rfl

/-- The upper endpoint flips sign; its norm has the positive reciprocal factor. -/
theorem highSize_step (n : ℕ) :
    O.highSize (n+1)=(((hi : ℝ)-O.tau n)/O.tau n)*O.highSize n := by
  have hb := O.lower_positive.trans O.endpoints_distinct
  have hα := O.alpha_positive n
  have hbound := (div_lt_iff hb).mp (O.alpha_interior n).1
  change ‖coordinates hH (O.state (n+1)).2 hi‖ = _
  rw [O.coordinate_norm_step hi n,abs_of_nonpos (by linarith only [hbound])]
  have hid : -(1-weightedAlpha H (O.weight n) (O.state n).1*(hi : ℝ)) =
      ((hi : ℝ)-O.tau n)/O.tau n := by
    rw [O.tau_eq_reciprocal]
    field_simp [hα.ne'] <;> ring
  rw [hid]
  rfl

/-- Constructor closing the operator-to-scalar endpoint-trajectory bridge. -/
def scalarTrajectory : BB.Defect.EndpointTrajectory (lo : ℝ) (hi : ℝ) where
  tau := O.tau
  lowSize := O.lowSize
  highSize := O.highSize
  tau_lower := fun n => (O.tau_interior n).1
  tau_upper := fun n => (O.tau_interior n).2
  low_initial := O.lowSize_positive 0
  high_initial := O.highSize_positive 0
  low_step := O.lowSize_step
  high_step := O.highSize_step

/-- The degree-one endpoint product of the actual current gradient. -/
def product (n : ℕ) : ℝ :=
  BB.geometricProduct (BB.endpointTheta (lo : ℝ) (hi : ℝ)) (O.lowSize n) (O.highSize n)

/-- Baseline endpoint energy of the actual current gradient. -/
def energy (n : ℕ) : ℝ := O.product n^2

def defect (n : ℕ) : ℝ := BB.endpointDefect (lo : ℝ) (hi : ℝ) (O.tau n)

def rate (_O : EndpointOperatorOrbit hH lo hi) : ℝ := BB.endpointRate (lo : ℝ) (hi : ℝ)

theorem rate_positive : 0 < O.rate := BB.endpointRate_pos O.lower_positive O.endpoints_distinct

theorem rate_lt_one : O.rate < 1 := BB.endpointRate_lt_one O.lower_positive O.endpoints_distinct

theorem product_positive (n : ℕ) : 0 < O.product n :=
  BB.geometricProduct_pos (O.lowSize_positive n) (O.highSize_positive n)

theorem energy_positive (n : ℕ) : 0 < O.energy n := sq_pos_of_pos (O.product_positive n)

theorem defect_nonnegative (n : ℕ) : 0 ≤ O.defect n :=
  BB.endpointDefect_nonneg O.lower_positive (O.tau_interior n).1 (O.tau_interior n).2

/-- The explicit powers in the manuscript are exactly this actual energy. -/
theorem energy_expanded (n : ℕ) :
    O.energy n=O.lowSize n^(2*BB.endpointTheta (lo : ℝ) (hi : ℝ))*
      O.highSize n^(2*(1-BB.endpointTheta (lo : ℝ) (hi : ℝ))) :=
  BB.geometricProduct_square (O.lowSize_positive n).le (O.highSize_positive n).le

/-- Exact one-step dissipation for the actual operator-gradient trajectory. -/
theorem energy_exact_step (n : ℕ) :
    O.energy (n+1)=O.rate^2*Real.exp (-2*O.defect n)*O.energy n :=
  O.scalarTrajectory.exact_step O.lower_positive n

/-- The exact cumulative identity now has actual gradients, projections and weights. -/
theorem energy_cumulative (n : ℕ) :
    O.energy n=O.rate^(2*n)*Real.exp (-2*∑ j in Finset.range n,O.defect j)*O.energy 0 :=
  O.scalarTrajectory.cumulative O.lower_positive n

/-- Worst-rate-normalized actual endpoint energy is nonincreasing. -/
theorem normalized_energy_antitone : Antitone (fun n => O.energy n/O.rate^(2*n)) :=
  O.scalarTrajectory.normalized_antitone O.lower_positive

/-- Positive lower limiting mean defect improves the actual energy root factor. -/
theorem strict_root_factor (hmean : 0 < liminf (BB.Defect.average O.defect) atTop) :
    limsup (BB.Defect.rootEnergy O.energy) atTop < O.rate^2 :=
  O.scalarTrajectory.strict_factor O.lower_positive hmean

/-- Full critical root-limit extremality is equivalent to vanishing mean defect. -/
theorem root_limit_iff_average_zero :
    Tendsto (BB.Defect.rootEnergy O.energy) atTop (𝓝 (O.rate^2)) ↔
      Tendsto (BB.Defect.average O.defect) atTop (𝓝 0) :=
  O.scalarTrajectory.root_limit_iff_average_zero O.lower_positive

/-- The weaker limsup hypothesis yields precisely a zero liminf of the mean. -/
theorem critical_limsup_mean (hroot : limsup (BB.Defect.rootEnergy O.energy) atTop=O.rate^2) :
    liminf (BB.Defect.average O.defect) atTop=0 :=
  O.scalarTrajectory.limsup_extremality O.lower_positive hroot

/-- Almost all actual reciprocal steps lie in every fixed midpoint neighborhood
when the actual endpoint energy has the full critical root limit. -/
theorem midpoint_concentration
    (hroot : Tendsto (BB.Defect.rootEnergy O.energy) atTop (𝓝 (O.rate^2)))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    Tendsto (BB.Defect.fraction (fun n => epsilon ≤ |O.tau n-((lo : ℝ)+(hi : ℝ))/2|))
      atTop (𝓝 0) :=
  O.scalarTrajectory.midpoint_concentration O.lower_positive hroot hepsilon

/-- Every actual current gradient on this endpoint tail is nonzero. -/
theorem gradient_norm_positive (n : ℕ) : 0 < ‖(O.state n).2‖ := by
  apply norm_pos_iff.mpr
  intro hzero
  have hp := (O.endpoints_present n).2.1
  apply hp
  simp [hzero,coordinates]

/-- Actual normalized spectral energies, grouped by distinct eigenspaces. -/
def normalizedSpectrum (n : ℕ) (mu : Eigenvalues H) : ℝ :=
  ‖coordinates hH (O.state n).2 mu‖^2/‖(O.state n).2‖^2

theorem normalizedSpectrum_nonnegative (n : ℕ) (mu : Eigenvalues H) :
    0 ≤ O.normalizedSpectrum n mu := div_nonneg (sq_nonneg _) (sq_nonneg _)

theorem normalizedSpectrum_sum (n : ℕ) : ∑ mu : Eigenvalues H,O.normalizedSpectrum n mu=1 := by
  unfold normalizedSpectrum
  rw [← Finset.sum_div,coordinates_sq_norm]
  exact div_self (sq_pos_of_pos (O.gradient_norm_positive n)).ne'

/-- The baseline transfer function evaluated on actual normalized endpoint energies. -/
def transfer (n : ℕ) : ℝ :=
  BB.Baseline.transfer (BB.endpointTheta (lo : ℝ) (hi : ℝ))
    (O.normalizedSpectrum n lo) (O.normalizedSpectrum n hi)

theorem transfer_log_identity (n : ℕ) :
    O.transfer n=Real.log ‖(O.state n).2‖-Real.log (O.product n) := by
  have ht := BB.Baseline.transfer_normalized (O.gradient_norm_positive n)
    (O.lowSize_positive n) (O.highSize_positive n) (BB.endpointTheta (lo : ℝ) (hi : ℝ))
  change O.transfer n=Real.log ‖(O.state n).2‖-
    Real.log (BB.geometricProduct (BB.endpointTheta (lo : ℝ) (hi : ℝ)) (O.lowSize n) (O.highSize n))
  unfold BB.geometricProduct
  rw [Real.log_mul (Real.rpow_pos_of_pos (O.lowSize_positive n) _).ne'
    (Real.rpow_pos_of_pos (O.highSize_positive n) _).ne',
    Real.log_rpow (O.lowSize_positive n),Real.log_rpow (O.highSize_positive n)]
  change O.transfer n=_ at ht
  linarith only [ht]

/-- Actual de-normalization, including equality with the square root of the energy. -/
theorem denormalization (n : ℕ) :
    ‖(O.state n).2‖*Real.exp (-O.transfer n)=O.product n ∧
      O.product n=Real.sqrt (O.energy n) := by
  constructor
  · exact BB.Baseline.denormalization (O.gradient_norm_positive n)
      (O.lowSize_positive n) (O.highSize_positive n) (BB.endpointTheta (lo : ℝ) (hi : ℝ))
  · exact (Real.sqrt_sq (O.product_positive n).le).symm

/-- Degree-one dissipation used in the actual coboundary identity. -/
theorem product_exact_step (n : ℕ) :
    O.product (n+1)=O.rate*Real.exp (-O.defect n)*O.product n := by
  have ht := O.tau_interior n
  have htp : 0 < O.tau n := O.lower_positive.trans ht.1
  unfold product
  rw [O.lowSize_step,O.highSize_step,
    BB.geometricProduct_mul (div_nonneg (sub_nonneg.mpr ht.1.le) htp.le)
      (div_nonneg (sub_nonneg.mpr ht.2.le) htp.le)
      (O.lowSize_positive n).le (O.highSize_positive n).le]
  change BB.endpointMultiplier (lo : ℝ) (hi : ℝ) (O.tau n)*_= _
  rw [BB.endpointMultiplier_defect_identity O.lower_positive ht.1 ht.2]
  rfl

/-- The exact multiplicative endpoint factor before logarithmic defects are introduced. -/
theorem product_multiplier_step (n : ℕ) :
    O.product (n+1)=BB.endpointMultiplier (lo : ℝ) (hi : ℝ) (O.tau n)*O.product n := by
  have ht := O.tau_interior n
  have htp : 0 < O.tau n := O.lower_positive.trans ht.1
  unfold product
  rw [O.lowSize_step,O.highSize_step]
  exact BB.geometricProduct_mul (div_nonneg (sub_nonneg.mpr ht.1.le) htp.le)
    (div_nonneg (sub_nonneg.mpr ht.2.le) htp.le)
    (O.lowSize_positive n).le (O.highSize_positive n).le

/-- The original exact-factor formula, for actual endpoint projection norms. -/
theorem energy_factor_step (n : ℕ) :
    O.energy (n+1)=
      ((O.tau n-(lo : ℝ))/O.tau n)^(2*BB.endpointTheta (lo : ℝ) (hi : ℝ))*
      (((hi : ℝ)-O.tau n)/O.tau n)^(2*(1-BB.endpointTheta (lo : ℝ) (hi : ℝ)))*
      O.energy n := by
  have ht := O.tau_interior n
  have htp : 0 < O.tau n := O.lower_positive.trans ht.1
  unfold energy
  rw [O.product_multiplier_step,mul_pow]
  congr 1
  exact BB.geometricProduct_square (div_nonneg (sub_nonneg.mpr ht.1.le) htp.le)
    (div_nonneg (sub_nonneg.mpr ht.2.le) htp.le)

/-- Positivity, critical contraction and strict decrease all hold along the actual orbit. -/
theorem energy_contraction (n : ℕ) :
    0 < O.energy (n+1) ∧ O.energy (n+1) ≤ O.rate^2*O.energy n ∧
      O.rate^2*O.energy n < O.energy n := by
  have he : Real.exp (-2*O.defect n) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith only [O.defect_nonnegative n])
  have hc2 : O.rate^2 < 1 := by
    nlinarith only [O.rate_positive,O.rate_lt_one]
  refine ⟨O.energy_positive (n+1),?_,?_⟩
  · rw [O.energy_exact_step]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left he (sq_nonneg O.rate)) (O.energy_positive n).le
    simpa only [mul_one] using hh
  · simpa only [one_mul] using mul_lt_mul_of_pos_right hc2 (O.energy_positive n)

/-- The de-normalized coboundary is exactly the logarithmic endpoint-product ratio. -/
theorem product_log_ratio (n : ℕ) :
    Real.log (O.product (n+1)/O.product n)=Real.log O.rate-O.defect n := by
  rw [Real.log_div (O.product_positive (n+1)).ne' (O.product_positive n).ne',
    O.product_exact_step,
    Real.log_mul (mul_pos O.rate_positive (Real.exp_pos _)).ne' (O.product_positive n).ne',
    Real.log_mul O.rate_positive.ne' (Real.exp_pos _).ne',Real.log_exp]
  ring

/-- The coboundary formula holds for the ratio of genuine consecutive gradient norms. -/
theorem gradient_norm_coboundary (n : ℕ) :
    Real.log (‖(O.state (n+1)).2‖/‖(O.state n).2‖)=
      Real.log O.rate-O.defect n+O.transfer (n+1)-O.transfer n := by
  rw [O.transfer_log_identity (n+1),O.transfer_log_identity n]
  exact BB.Baseline.coboundary_identity (O.gradient_norm_positive n)
    (O.gradient_norm_positive (n+1)) (O.product_positive n) O.rate_positive (O.product_exact_step n)

end EndpointOperatorOrbit
end BB.Operator
