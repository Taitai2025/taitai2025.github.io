import BB.EuclideanSystem
import BB.EuclideanGeometry
import BB.Certificate

/-! # Exact Euclidean estimates for the actual rescaled BB maps

All assumptions are those of `System`; the constants below are the literal
Euclidean B and L of the manuscript.
-/

set_option autoImplicit false
noncomputable section
namespace BB.Euclidean.System
open BB.Operator BB.Gluing

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable (s : System E Ω)

def step (w : Ω) (z : Pair E) : Pair E := T s.H (s.W w) z
def scaled (r : ℝ) (w : Ω) (z : Pair E) : Pair E := r⁻¹ • s.step w z
def domain (lo hi : Fin (s.n+2)) : Set (Pair E) := stateSet s.symmetric s.card s.M lo hi
def endpoint (lo hi : Fin (s.n+2)) : Pair E → ℝ := P s.symmetric s.card lo hi

theorem step_smul (w : Ω) (z : Pair E) (t : ℝ) :
    s.step w (t • z)=t • s.step w z := by
  unfold step T
  rw [toPair_smul,stateMap_smul,ofPair_smul]

@[simp] theorem step_zero (w : Ω) : s.step w 0=0 := T_zero _ _
@[simp] theorem scaled_zero (r : ℝ) (w : Ω) : s.scaled r w 0=0 := by simp [scaled]

theorem scaled_smul (r : ℝ) (w : Ω) (z : Pair E) (t : ℝ) :
    s.scaled r w (t • z)=t • s.scaled r w z := by
  simp only [scaled,s.step_smul,smul_smul]
  rw [mul_comm]

theorem step_cone (w : Ω) {z : Pair E} (hz : cone s.M z) : cone s.M (s.step w z) :=
  stateMap_cone s.symmetric (s.commute w) (s.weight_positive w)
    s.lower_pos s.lower_lt_upper.le s.spectral_bounds s.M_growth hz

theorem domain_scale {lo hi : Fin (s.n+2)} {z : Pair E}
    (hz : z ∈ s.domain lo hi) (t : ℝ) : t • z ∈ s.domain lo hi :=
  stateSet_smul s.symmetric s.card hz t

theorem step_mem {lo hi : Fin (s.n+2)} (w : Ω) {z : Pair E}
    (hz : z ∈ s.domain lo hi) : s.step w z ∈ s.domain lo hi :=
  T_mem_of_cone s.symmetric s.card hz (s.step_cone w hz.1)

theorem scaled_mem {lo hi : Fin (s.n+2)} (r : ℝ) (w : Ω) {z : Pair E}
    (hz : z ∈ s.domain lo hi) : s.scaled r w z ∈ s.domain lo hi :=
  s.domain_scale (s.step_mem w hz) r⁻¹

theorem step_growth (w : Ω) {z : Pair E} (hz : cone s.M z) :
    ‖s.step w z‖≤s.B*‖z‖ := by
  rw [norm_eq_pairNorm,norm_eq_pairNorm]
  exact stateMap_growth s.symmetric (s.commute w) (s.weight_positive w)
    s.lower_pos s.lower_lt_upper.le s.spectral_bounds (toPair z) hz

theorem step_lipschitz (w : Ω) {x y : Pair E} (hx : cone s.M x) (hy : cone s.M y) :
    ‖s.step w x-s.step w y‖≤s.L*‖x-y‖ := by
  letI := s.weight_nonempty w
  rw [norm_eq_pairNorm,norm_eq_pairNorm]
  exact stateMap_lipschitz s.symmetric (s.weight_symmetric w) (s.weight_positive w)
    (s.commute w) s.lower_pos s.lower_lt_upper.le s.M_nonneg s.chi_nonneg
    s.spectral_bounds (s.weight_condition w) (toPair x) (toPair y) hx hy

theorem scaled_growth {r : ℝ} (hr : 0<r) (w : Ω) {z : Pair E} (hz : cone s.M z) :
    ‖s.scaled r w z‖≤(s.B/r)*‖z‖ := by
  rw [scaled,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  calc
    r⁻¹*‖s.step w z‖≤r⁻¹*(s.B*‖z‖) :=
      mul_le_mul_of_nonneg_left (s.step_growth w hz) (inv_nonneg.mpr hr.le)
    _ = (s.B/r)*‖z‖ := by ring

theorem scaled_bound {r : ℝ} (hr : 0<r) (w : Ω) {z : Pair E} (hz : cone s.M z) :
    ‖s.scaled r w z‖≤(s.L/r)*‖z‖ :=
  (s.scaled_growth hr w hz).trans
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right s.B_le_L hr.le) (norm_nonneg z))

theorem scaled_lipschitz {r : ℝ} (hr : 0<r) (w : Ω) {x y : Pair E}
    (hx : cone s.M x) (hy : cone s.M y) :
    ‖s.scaled r w x-s.scaled r w y‖≤(s.L/r)*‖x-y‖ := by
  rw [scaled,scaled,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
  calc
    r⁻¹*‖s.step w x-s.step w y‖≤r⁻¹*(s.L*‖x-y‖) :=
      mul_le_mul_of_nonneg_left (s.step_lipschitz w hx hy) (inv_nonneg.mpr hr.le)
    _ = (s.L/r)*‖x-y‖ := by ring

theorem step_eq_scale_scaled {r : ℝ} (hr : r≠0) (w : Ω) (z : Pair E) :
    s.step w z=r • s.scaled r w z := by
  rw [scaled,smul_smul,mul_inv_cancel hr,one_smul]

theorem endpoint_scaled_step {lo hi : Fin (s.n+2)} (hlohi : lo<hi)
    (w : Ω) {z : Pair E} (hz : z ∈ s.domain lo hi) :
    s.endpoint lo hi (s.scaled (s.faceRate lo hi) w z)≤s.endpoint lo hi z := by
  have hc := s.faceRate_pos hlohi
  unfold scaled endpoint
  rw [P_homogeneous s.symmetric s.card (s.lam_pos lo) hlohi _ (inv_nonneg.mpr hc.le)]
  have hp := P_step s.symmetric s.card (s.commute w) (s.weight_positive w) (s.lam_pos lo) hlohi hz
  calc
    (s.faceRate lo hi)⁻¹*P s.symmetric s.card lo hi (s.step w z) ≤
        (s.faceRate lo hi)⁻¹*(s.faceRate lo hi*P s.symmetric s.card lo hi z) :=
      mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr hc.le)
    _ = P s.symmetric s.card lo hi z := by rw [← mul_assoc,inv_mul_cancel hc.ne',one_mul]

theorem run_scaled {r : ℝ} (hr : 0≤r) (l : List Ω) (z : Pair E) :
    run (s.scaled r) l z=r⁻¹^l.length • run s.step l z := by
  exact run_rescaled (C := Set.univ) (inv_nonneg.mpr hr)
    (fun _ _ _ => Set.mem_univ _) (fun _ _ _ _ => Set.mem_univ _)
    (fun w z _ t _ => s.step_smul w z t) l (Set.mem_univ z)

theorem rescaled_word_bound {lo hi : Fin (s.n+2)} {c r : ℝ}
    (v : Certificate s.step (s.domain lo hi) c) (hc : 0≤c) (hr : 0<r)
    (l : List Ω) {z : Pair E} (hz : z ∈ s.domain lo hi) :
    ‖run (s.scaled r) l z‖≤v.prefactor*(c/r)^l.length*‖z‖ := by
  rw [s.run_scaled hr.le,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hr.le) _)]
  calc
    r⁻¹^l.length*‖run s.step l z‖≤
        r⁻¹^l.length*(v.prefactor*c^l.length*‖z‖) :=
      mul_le_mul_of_nonneg_left
        (v.word_bound hc (fun w z hz => s.step_mem w hz) l hz)
        (pow_nonneg (inv_nonneg.mpr hr.le) _)
    _ = v.prefactor*(c/r)^l.length*‖z‖ := by rw [div_eq_mul_inv,mul_pow]; ring

end BB.Euclidean.System
