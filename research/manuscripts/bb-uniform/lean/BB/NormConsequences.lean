import BB.BlockNorms
import Mathlib.Tactic

/-! # Error and objective-gap consequences, with exact exponents -/

noncomputable section
namespace BB.Consequences

open BB.Blocks
open scoped BigOperators

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]

def quadraticGap (lam : ι → ℝ) (g : ∀ i, E i) : ℝ :=
  ∑ i, ‖g i‖^2 / (2*lam i)

/-- The exact objective gap expressed in gradient coordinates. -/
theorem quadratic_gap_comparison {lam : ι → ℝ} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hlow : ∀ i, a ≤ lam i) (hhigh : ∀ i, lam i ≤ b)
    (g : ∀ i, E i) :
    (blockL2 g)^2/(2*b) ≤ quadraticGap lam g ∧
      quadraticGap lam g ≤ (blockL2 g)^2/(2*a) := by
  have hb : 0 < b := ha.trans_le hab
  rw [blockL2_sq]
  unfold quadraticGap
  rw [Finset.sum_div,Finset.sum_div]
  constructor
  · apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith [hlow i]) (by linarith [hhigh i])
  · apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_left (sq_nonneg _) (by linarith) (by linarith [hlow i])

theorem quadraticGap_eq_error_energy (lam : ι → ℝ) (e : ∀ i, E i)
    (hlam : ∀ i, 0 < lam i) :
    quadraticGap lam (fun i => lam i • e i) = (1/2 : ℝ) * ∑ i, lam i * ‖e i‖^2 := by
  unfold quadraticGap
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hlam i)]
  field_simp [(hlam i).ne']
  <;> ring

theorem matched_pair_norm (g : ∀ i, E i) :
    stateL2 (g,g) = Real.sqrt 2 * blockL2 g := by
  have hs : 0 ≤ ∑ i, ‖g i‖^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  unfold stateL2 blockL2
  rw [show (∑ i, ‖g i‖^2) + (∑ i, ‖g i‖^2) = 2 * (∑ i, ‖g i‖^2) by ring]
  exact Real.sqrt_mul (by norm_num) _

/-- Transfer of a gradient estimate to errors by a fixed norm equivalence. -/
theorem error_bound_from_gradient {a b K t e e₀ g g₀ : ℝ}
    (ha : 0 < a) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (helow : a*e ≤ g) (hehigh : g₀ ≤ b*e₀) (hgrad : g ≤ K*t*g₀) :
    e ≤ (b/a)*K*t*e₀ := by
  have h := mul_le_mul_of_nonneg_left hehigh (mul_nonneg hK ht)
  have hid : (b/a)*K*t*e₀ = (b*K*t*e₀)/a := by ring
  rw [hid]
  apply (le_div_iff ha).mpr
  linarith

/-- Squaring a gradient bound yields precisely the squared rate for gaps. -/
theorem gap_bound_from_gradient {a b K t d d₀ g g₀ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hK : 0 ≤ K) (ht : 0 ≤ t)
    (hg : 0 ≤ g) (hg₀ : 0 ≤ g₀)
    (hgap : d ≤ g^2/(2*a)) (hgap₀ : g₀^2/(2*b) ≤ d₀)
    (hgrad : g ≤ K*t*g₀) : d ≤ (b/a)*K^2*t^2*d₀ := by
  have hgsq : g^2 ≤ (K*t*g₀)^2 := by
    have hsum : 0 ≤ K*t*g₀ + g := by positivity
    have h := mul_nonneg (sub_nonneg.mpr hgrad) hsum
    nlinarith only [h]
  have h0 : g₀^2 ≤ (2*b)*d₀ := by
    have := (div_le_iff (by positivity : 0 < 2*b)).mp hgap₀
    nlinarith only [this]
  have h2 := mul_le_mul_of_nonneg_left h0 (mul_nonneg (sq_nonneg K) (sq_nonneg t))
  have hd : (2*a)*d ≤ g^2 := by
    have := (le_div_iff (by positivity : 0 < 2*a)).mp hgap
    nlinarith only [this]
  have hid : (2*a)*((b/a)*K^2*t^2*d₀) = (K^2*t^2)*((2*b)*d₀) := by
    field_simp
    <;> ring
  apply (mul_le_mul_left (by positivity : 0 < 2*a)).mp
  rw [hid]
  nlinarith only [hd,hgsq,h2]

theorem squared_rate (c : ℝ) (k : ℕ) : (c^k)^2 = c^(2*k) := by
  rw [← pow_mul]
  congr 1
  omega

end BB.Consequences
