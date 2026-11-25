import BB.Certificate
import BB.Dini

/-! # Guarded local bootstrap and the Lyapunov perturbation step

The state-set and secant estimates are explicit hypotheses in these reusable
lemmas. The conclusions do not silently assert that those hypotheses follow
from a Hessian modulus; that analytical bridge is proved separately.
-/

noncomputable section
namespace BB.Local

open BB.Gluing

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lyapunov_perturbation {T : W → E → E} {C : Set E} {c A B : ℝ}
    (v : Certificate T C c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (omega : ℝ → ℝ) (hmono : Monotone omega)
    (homega : ∀ t, 0 ≤ t → 0 ≤ omega t)
    (w : W) {z z' : E} (hz : z ∈ C) (hz' : z' ∈ C) (hT : T w z ∈ C)
    (herr : ‖z'-T w z‖ ≤ A * omega (B*‖z‖) * ‖z‖) :
    v.value z' ≤ (c + v.lipConstant*A*omega (B*v.value z)) * v.value z := by
  have hnorm := v.lower z hz
  have hv0 : 0 ≤ v.value z := (norm_nonneg _).trans hnorm
  have ho : omega (B*‖z‖) ≤ omega (B*v.value z) :=
    hmono (mul_le_mul_of_nonneg_left hnorm hB)
  have ho0 : 0 ≤ omega (B*‖z‖) := homega _ (mul_nonneg hB (norm_nonneg _))
  have he := mul_le_mul_of_nonneg_left herr v.lipConstant_nonneg
  have hh := (le_abs_self (v.value z' - v.value (T w z))).trans (v.lipschitz z' (T w z) hz' hT)
  have ht := v.decrease w z hz
  have hp := mul_le_mul ho hnorm (norm_nonneg z) (homega _ (mul_nonneg hB hv0))
  have hp' := mul_le_mul_of_nonneg_left hp (mul_nonneg v.lipConstant_nonneg hA)
  nlinarith only [he,hh,ht,hp']

/-- A proposed next iterate is checked before the local recurrence is used.
This rules out circular assumptions that all future secants stay in the ball. -/
theorem guarded_bootstrap (x : ℕ → E) (v : ℕ → ℝ) (omega : ℝ → ℝ)
    (c D B gamma epsilon R Q : ℝ)
    (hv : ∀ n, 0 ≤ v n) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hgamma : 0 ≤ gamma) (hgamma1 : gamma ≤ 1) (hQ : 0 ≤ Q)
    (hmono : Monotone omega) (hinit : v 0 ≤ epsilon)
    (hx0 : ‖x 0‖ < R) (hx1 : ‖x 1‖ < R)
    (hball : Q*epsilon < R) (hsmall : c + D*omega (B*epsilon) ≤ gamma)
    (hnext : ∀ n, ‖x n‖ < R → ‖x (n+1)‖ < R → v n ≤ epsilon →
      ‖x (n+2)‖ ≤ Q*v n)
    (hrec : ∀ n, ‖x n‖ < R → ‖x (n+1)‖ < R → ‖x (n+2)‖ < R →
      v (n+1) ≤ (c + D*omega (B*v n))*v n) :
    (∀ n, ‖x n‖ < R) ∧ (∀ n, v n ≤ gamma^n * v 0) ∧
      (∀ n, v (n+1) ≤ (c + D*omega (B*v n))*v n) := by
  have joint : ∀ n, ‖x n‖ < R ∧ ‖x (n+1)‖ < R ∧ v n ≤ gamma^n*v 0 := by
    intro n
    induction n with
    | zero => exact ⟨hx0,hx1,by simp⟩
    | succ n ih =>
      have hpow : gamma^n ≤ 1 := pow_le_one n hgamma hgamma1
      have hve : v n ≤ epsilon :=
        (ih.2.2.trans (by nlinarith only [hpow,hv 0])).trans hinit
      have hxn : ‖x (n+2)‖ < R :=
        (hnext n ih.1 ih.2.1 hve).trans_lt
          ((mul_le_mul_of_nonneg_left hve hQ).trans_lt hball)
      have ho : omega (B*v n) ≤ omega (B*epsilon) :=
        hmono (mul_le_mul_of_nonneg_left hve hB)
      have hcoef : c + D*omega (B*v n) ≤ gamma := by
        have h := mul_le_mul_of_nonneg_left ho hD
        linarith
      have hstep : v (n+1) ≤ gamma*v n :=
        (hrec n ih.1 ih.2.1 hxn).trans (mul_le_mul_of_nonneg_right hcoef (hv n))
      refine ⟨ih.2.1,by simpa only [Nat.add_assoc] using hxn,?_⟩
      calc
        v (n+1) ≤ gamma*v n := hstep
        _ ≤ gamma*(gamma^n*v 0) := mul_le_mul_of_nonneg_left ih.2.2 hgamma
        _ = gamma^(n+1)*v 0 := by rw [pow_succ]; ring
  refine ⟨fun n => (joint n).1, fun n => (joint n).2.2, ?_⟩
  intro n
  exact hrec n (joint n).1 (joint n).2.1 (joint (n+1)).2.1

open MeasureTheory

/-- Exact critical factor after the local bootstrap, with one uniform Dini
prefactor for every initial value at most `epsilon`. -/
theorem guarded_critical_rate (x : ℕ → E) (v : ℕ → ℝ) (omega : ℝ → ℝ)
    (c D B gamma epsilon R Q : ℝ)
    (hc : 0 < c) (hv : ∀ n, 0 ≤ v n) (hD : 0 ≤ D) (hB : 0 < B)
    (hgamma : 0 < gamma) (hgamma1 : gamma < 1) (hepsilon : 0 < epsilon) (hQ : 0 ≤ Q)
    (hmono : Monotone omega) (homega : ∀ t, 0 ≤ t → 0 ≤ omega t) (hinit : v 0 ≤ epsilon)
    (hx0 : ‖x 0‖ < R) (hx1 : ‖x 1‖ < R)
    (hball : Q*epsilon < R) (hsmall : c + D*omega (B*epsilon) ≤ gamma)
    (hnext : ∀ n, ‖x n‖ < R → ‖x (n+1)‖ < R → v n ≤ epsilon →
      ‖x (n+2)‖ ≤ Q*v n)
    (hrec : ∀ n, ‖x n‖ < R → ‖x (n+1)‖ < R → ‖x (n+2)‖ < R →
      v (n+1) ≤ (c + D*omega (B*v n))*v n)
    (hDini : IntervalIntegrable (fun t => omega t/t) volume 0 (B*epsilon)) :
    (∀ n, ‖x n‖ < R) ∧ ∀ n, v n ≤ c^n*v 0 *
      Real.exp ((D/c)*(omega (B*epsilon) +
        (∫ t in (0 : ℝ)..(B*epsilon), omega t/t)/(-Real.log gamma))) := by
  obtain ⟨hstay,hrough,hrec'⟩ := guarded_bootstrap x v omega c D B gamma epsilon R Q
    hv hD hB.le hgamma.le hgamma1.le hQ hmono hinit hx0 hx1 hball hsmall hnext hrec
  refine ⟨hstay, ?_⟩
  exact BB.Dini.uniform_critical_rate_of_dini v omega c D B gamma epsilon hc hv hD hB
    hepsilon hgamma hgamma1 hmono homega hinit hsmall hrec' hDini

end BB.Local
