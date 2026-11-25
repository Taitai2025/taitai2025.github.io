import BB.Initialization
import BB.OperatorFaceStep
import BB.RecursiveConstants

set_option autoImplicit false

noncomputable section
namespace BB.Operator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem weightedAlpha_smul (H W : E →ₗ[ℝ] E) (u : E) {t : ℝ} (ht : t ≠ 0) :
    weightedAlpha H W (t • u) = weightedAlpha H W u := by
  unfold weightedAlpha
  simp only [map_smul,real_inner_smul_left,inner_smul_right]
  have hN : t*(t*@inner ℝ _ _ u (W u)) = t^2*@inner ℝ _ _ u (W u) := by ring
  have hD : t*(t*@inner ℝ _ _ u (W (H u))) = t^2*@inner ℝ _ _ u (W (H u)) := by ring
  rw [hN,hD]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 ht)

theorem stateMap_smul (H W : E →ₗ[ℝ] E) (z : E × E) (t : ℝ) :
    stateMap H W (t • z) = t • stateMap H W z := by
  by_cases ht : t = 0
  · simp [ht,stateMap_zero]
  apply Prod.ext
  · rfl
  · change t • z.2-weightedAlpha H W (t • z.1) • H (t • z.2) =
      t • (z.2-weightedAlpha H W z.1 • H z.2)
    rw [weightedAlpha_smul H W z.1 ht,H.map_smul,smul_sub,smul_smul,smul_smul,mul_comm]

end BB.Operator

namespace BB.Euclidean
open Module.End BB.Operator

variable (E Ω : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Only the source's actual operator, positive commuting weights, condition
bound and cone assumptions. No rate or boundary estimate is a field. -/
structure System where
  H : E →ₗ[ℝ] E
  symmetric : H.IsSymmetric
  n : ℕ
  card : Fintype.card (Eigenvalues H) = n+2
  positive : ∀ x : E, x ≠ 0 → 0 < @inner ℝ _ _ x (H x)
  chi : ℝ
  chi_ge_one : 1 ≤ chi
  M : ℝ
  M_ge_one : 1 ≤ M
  M_growth : sortedLambda H card (Fin.last (n+1))/sortedLambda H card 0-1 ≤ M
  W : Ω → E →ₗ[ℝ] E
  weight_symmetric : ∀ w, (W w).IsSymmetric
  weight_positive : ∀ w x, x ≠ 0 → 0 < @inner ℝ _ _ x (W w x)
  commute : ∀ w, Function.Commute H (W w)
  weight_nonempty : ∀ w, Nonempty (Eigenvalues (W w))
  weight_condition : ∀ w, letI := weight_nonempty w; spectralConditionNumber (W w) ≤ chi

variable {E Ω}

namespace System

variable (s : System E Ω)

def lam : Fin (s.n+2) → ℝ := sortedLambda s.H s.card
def lower : ℝ := s.lam 0
def upper : ℝ := s.lam (Fin.last (s.n+1))
def B : ℝ := growthConstant s.lower s.upper
def L : ℝ := operatorLipConstant s.lower s.upper s.M s.chi
def faceRate (lo hi : Fin (s.n+2)) : ℝ := BB.endpointRate (s.lam lo) (s.lam hi)
def faceLength (lo hi : Fin (s.n+2)) : ℕ :=
  BB.Recursive.length (BB.Recursive.extend s.lam) s.B s.L lo.val (hi.val-lo.val)
def facePrefactor (lo hi : Fin (s.n+2)) : ℝ :=
  BB.Recursive.prefactor (BB.Recursive.extend s.lam) s.B s.L lo.val (hi.val-lo.val)

theorem lam_strictMono : StrictMono s.lam := sortedLambda_strictMono s.H s.card
theorem lam_pos (i : Fin (s.n+2)) : 0 < s.lam i := sortedLambda_pos s.card s.positive i
theorem lower_pos : 0 < s.lower := s.lam_pos 0
theorem lower_lt_upper : s.lower < s.upper := s.lam_strictMono (by change 0 < s.n+1; omega)
theorem M_nonneg : 0 ≤ s.M := (by norm_num : (0 : ℝ) ≤ 1).trans s.M_ge_one
theorem chi_nonneg : 0 ≤ s.chi := (by norm_num : (0 : ℝ) ≤ 1).trans s.chi_ge_one
theorem spectral_bounds (mu : Eigenvalues s.H) : s.lower ≤ (mu:ℝ) ∧ (mu:ℝ) ≤ s.upper :=
  sorted_spectral_bounds s.H s.card mu

theorem B_ge_one : 1 ≤ s.B := by
  unfold B growthConstant
  exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by nlinarith [sq_nonneg (s.upper/s.lower-1)])

theorem B_le_L : s.B ≤ s.L :=
  (growthConstant_le_ratio s.lower_pos s.lower_lt_upper.le).trans
    (ratio_le_operatorLipConstant s.lower_pos s.lower_lt_upper.le s.M_nonneg)

theorem L_ge_one : 1 ≤ s.L := s.B_ge_one.trans s.B_le_L

theorem faceRate_pos {lo hi : Fin (s.n+2)} (hlohi : lo < hi) : 0 < s.faceRate lo hi :=
  BB.endpointRate_pos (s.lam_pos lo) (s.lam_strictMono hlohi)

theorem faceRate_lt_one {lo hi : Fin (s.n+2)} (hlohi : lo < hi) : s.faceRate lo hi < 1 :=
  BB.endpointRate_lt_one (s.lam_pos lo) (s.lam_strictMono hlohi)

theorem natRate_eq {lo hi : Fin (s.n+2)} (hlohi : lo ≤ hi) :
    BB.Recursive.rate (BB.Recursive.extend s.lam) lo.val (hi.val-lo.val) = s.faceRate lo hi := by
  unfold BB.Recursive.rate faceRate
  rw [Nat.add_sub_of_le hlohi,BB.Recursive.extend_fin,BB.Recursive.extend_fin]

theorem faceLength_ge_three {lo hi : Fin (s.n+2)} (hlohi : lo < hi) : 3 ≤ s.faceLength lo hi :=
  BB.Recursive.length_ge_three _ _ _ _ _ (Nat.sub_pos_of_lt hlohi)

theorem facePrefactor_eq {lo hi : Fin (s.n+2)} (hlohi : lo < hi) :
    s.facePrefactor lo hi = 2*(s.L/s.faceRate lo hi)^(s.faceLength lo hi) := by
  unfold facePrefactor faceLength
  rw [BB.Recursive.prefactor_eq _ _ _ _ _ (Nat.sub_pos_of_lt hlohi),s.natRate_eq hlohi.le]

theorem facePrefactor_ge_one {lo hi : Fin (s.n+2)} (hlohi : lo < hi) :
    1 ≤ s.facePrefactor lo hi := by
  unfold facePrefactor
  apply BB.Recursive.prefactor_ge_one _ _ _ _ _ (Nat.sub_pos_of_lt hlohi)
  · rw [s.natRate_eq hlohi.le]
    exact s.faceRate_pos hlohi
  · rw [s.natRate_eq hlohi.le]
    exact (s.faceRate_lt_one hlohi).le.trans s.L_ge_one

end System
end BB.Euclidean
