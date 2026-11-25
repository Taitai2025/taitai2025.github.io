import BB.SpectralFaces
import BB.StateLipschitz
import BB.Certificate

/-! # Rescaling the actual diagonal spectral BB family -/

noncomputable section
namespace BB.Diagonal

open BB.Spectral BB.Faces BB.Gluing

variable {n : ℕ}

def Weights (n : ℕ) (χ : ℝ) := {w : Fin n → ℝ // ∀ i, 1 ≤ w i ∧ w i ≤ χ}

def T (lam : Fin n → ℝ) {χ : ℝ} (w : Weights n χ) (z : State (Fin n)) :=
  stateMap lam w.val z

def S (lam : Fin n → ℝ) (r : ℝ) {χ : ℝ} (w : Weights n χ) (z : State (Fin n)) :=
  r⁻¹ • T lam w z

def scaledLip (n : ℕ) (a b χ M r : ℝ) := max 1 (r⁻¹ * stateLip (Fin n) a b χ M)

theorem scaledLip_ge_one (n : ℕ) (a b χ M r : ℝ) : 1 ≤ scaledLip n a b χ M r :=
  le_max_left _ _

theorem T_mem {lam : Fin n → ℝ} {a b χ M : ℝ} {lo hi : Fin n}
    (ha : 0 < a) (hab : a ≤ b)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (w : Weights n χ) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi) :
    T lam w z ∈ stateSet M lo hi :=
  stateMap_mem ha hab (fun i => (w.property i).1) hlama hlamb hM hz

theorem S_mem {lam : Fin n → ℝ} {a b χ M r : ℝ} {lo hi : Fin n}
    (ha : 0 < a) (hab : a ≤ b)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (w : Weights n χ) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi) :
    S lam r w z ∈ stateSet M lo hi :=
  stateSet_smul (T_mem ha hab hlama hlamb hM w hz) r⁻¹

@[simp] theorem T_zero (lam : Fin n → ℝ) {χ : ℝ} (w : Weights n χ) : T lam w 0 = 0 :=
  stateMap_zero lam w.val

@[simp] theorem S_zero (lam : Fin n → ℝ) (r : ℝ) {χ : ℝ} (w : Weights n χ) : S lam r w 0 = 0 := by
  simp [S]

theorem T_smul (lam : Fin n → ℝ) {χ : ℝ} (w : Weights n χ)
    (z : State (Fin n)) (t : ℝ) : T lam w (t • z) = t • T lam w z :=
  stateMap_smul lam w.val z t

theorem S_smul (lam : Fin n → ℝ) (r : ℝ) {χ : ℝ} (w : Weights n χ)
    (z : State (Fin n)) (t : ℝ) : S lam r w (t • z) = t • S lam r w z := by
  unfold S
  rw [T_smul, smul_comm]

theorem T_eq_scale_S (lam : Fin n → ℝ) {r χ : ℝ} (hr : r ≠ 0)
    (w : Weights n χ) (z : State (Fin n)) : T lam w z = r • S lam r w z := by
  simp [S, smul_smul, hr]

theorem S_lipschitz {lam : Fin n → ℝ} {a b χ M r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM0 : 0 ≤ M) (hr : 0 < r)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (w : Weights n χ) {z z' : State (Fin n)} (hz : Cone M z) (hz' : Cone M z') :
    ‖S lam r w z - S lam r w z'‖ ≤ scaledLip n a b χ M r * ‖z-z'‖ := by
  unfold S
  rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le)]
  calc
    r⁻¹ * ‖T lam w z - T lam w z'‖ ≤ r⁻¹ * (stateLip (Fin n) a b χ M * ‖z-z'‖) :=
      mul_le_mul_of_nonneg_left (stateMap_lipschitz ha hab hχ hM0
        (fun i => (w.property i).1) (fun i => (w.property i).2) hlama hlamb hz hz')
        (inv_nonneg.mpr hr.le)
    _ = (r⁻¹ * stateLip (Fin n) a b χ M) * ‖z-z'‖ := by ring
    _ ≤ scaledLip n a b χ M r * ‖z-z'‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

theorem S_bound {lam : Fin n → ℝ} {a b χ M r : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hχ : 0 ≤ χ) (hM0 : 0 ≤ M) (hr : 0 < r)
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b)
    (w : Weights n χ) {z : State (Fin n)} (hz : Cone M z) :
    ‖S lam r w z‖ ≤ scaledLip n a b χ M r * ‖z‖ := by
  have h := S_lipschitz ha hab hχ hM0 hr hlama hlamb w hz (show Cone M 0 by simp [Cone])
  simpa using h

theorem endpointProduct_S {lam : Fin n → ℝ} {lo hi : Fin n} {M r χ : ℝ}
    (hpos : 0 < lam lo) (hmono : StrictMono lam) (hlohi : lo < hi) (hr : 0 < r)
    (hcr : BB.endpointRate (lam lo) (lam hi) ≤ r)
    (w : Weights n χ) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi) :
    endpointProduct lam lo hi (S lam r w z) ≤ endpointProduct lam lo hi z := by
  unfold S
  rw [endpointProduct_homogeneous hpos (hmono hlohi) _ (inv_nonneg.mpr hr.le)]
  have ht := endpointProduct_step hpos hmono hlohi (fun i => (w.property i).1) hz
  have hmul := mul_le_mul_of_nonneg_right hcr (endpointProduct_nonneg lam lo hi z)
  have h := mul_le_mul_of_nonneg_left (ht.trans hmul) (inv_nonneg.mpr hr.le)
  simpa only [← mul_assoc, inv_mul_cancel hr.ne', one_mul] using h

theorem rescaled_word_bound {lam : Fin n → ℝ} {a b χ M r r' : ℝ} {lo hi : Fin n}
    (ha : 0 < a) (hab : a ≤ b) (hr : 0 < r) (hr' : 0 ≤ r')
    (hlama : ∀ i, a ≤ lam i) (hlamb : ∀ i, lam i ≤ b) (hM : b/a-1 ≤ M)
    (v : Certificate (T lam (χ := χ)) (stateSet M lo hi) r')
    (l : List (Weights n χ)) {z : State (Fin n)} (hz : z ∈ stateSet M lo hi) :
    ‖run (S lam r) l z‖ ≤ v.prefactor * (r'/r)^l.length * ‖z‖ := by
  have hT := fun (w : Weights n χ) z (hz : z ∈ stateSet M lo hi) =>
    T_mem ha hab hlama hlamb hM w hz
  have heq := run_rescaled (inv_nonneg.mpr hr.le) hT
    (fun z hz t _ => stateSet_smul hz t) (fun w z _ t _ => T_smul lam w z t) l hz
  change run (S lam r) l z = r⁻¹^l.length • run (T lam) l z at heq
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _)]
  have hb := v.word_bound hr' hT l hz
  calc
    r⁻¹^l.length * ‖run (T lam) l z‖ ≤
        r⁻¹^l.length * (v.prefactor * r'^l.length * ‖z‖) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg (inv_nonneg.mpr hr.le) _)
    _ = v.prefactor * (r'/r)^l.length * ‖z‖ := by
      rw [div_eq_mul_inv, mul_pow]
      ring

end BB.Diagonal
