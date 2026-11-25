import BB.Boundary

/-! # Complete finite-horizon certificate, with every input exposed -/

noncomputable section
namespace BB.Gluing

variable {E W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A common homogeneous Lipschitz Lyapunov certificate on a state set.
This is data to be constructed, not an axiom or an opaque proof assumption. -/
structure Certificate (T : W → E → E) (C : Set E) (c : ℝ) where
  value : E → ℝ
  prefactor : ℝ
  lipConstant : ℝ
  prefactor_ge_one : 1 ≤ prefactor
  lipConstant_nonneg : 0 ≤ lipConstant
  lower : ∀ z ∈ C, ‖z‖ ≤ value z
  upper : ∀ z ∈ C, value z ≤ prefactor * ‖z‖
  lipschitz : ∀ x y, x ∈ C → y ∈ C → |value x - value y| ≤ lipConstant * ‖x-y‖
  homogeneous : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → value (t • z) = t * value z
  decrease : ∀ w z, z ∈ C → value (T w z) ≤ c * value z

theorem Certificate.word_bound {T : W → E → E} {C : Set E} {c : ℝ}
    (v : Certificate T C c) (hc : 0 ≤ c)
    (hT : ∀ w z, z ∈ C → T w z ∈ C)
    (l : List W) {z : E} (hz : z ∈ C) :
    ‖run T l z‖ ≤ v.prefactor * c^l.length * ‖z‖ := by
  have h : ∀ (l : List W) (z : E), z ∈ C →
      v.value (run T l z) ≤ c^l.length * v.value z := by
    intro l
    induction l with
    | nil => intro z hz; simp
    | cons w l ih =>
      intro z hz
      calc
        v.value (run T (w :: l) z) ≤ c^l.length * v.value (T w z) :=
          ih _ (hT w z hz)
        _ ≤ c^l.length * (c * v.value z) :=
          mul_le_mul_of_nonneg_left (v.decrease w z hz) (pow_nonneg hc _)
        _ = c^(w :: l).length * v.value z := by simp only [List.length_cons, pow_succ]; ring
  calc
    ‖run T l z‖ ≤ v.value (run T l z) := v.lower _ (run_mem hT l hz)
    _ ≤ c^l.length * v.value z := h l z hz
    _ ≤ c^l.length * (v.prefactor * ‖z‖) :=
      mul_le_mul_of_nonneg_left (v.upper z hz) (pow_nonneg hc _)
    _ = v.prefactor * c^l.length * ‖z‖ := by ring

theorem Certificate.trajectory_bound {T : W → E → E} {C : Set E} {c : ℝ}
    (v : Certificate T C c) (hc : 0 ≤ c)
    (z : ℕ → E) (w : ℕ → W) (hz : ∀ k, z k ∈ C)
    (hrec : ∀ k, z (k+1) = T (w k) (z k)) (k : ℕ) :
    ‖z k‖ ≤ v.prefactor * c^k * ‖z 0‖ :=
  BB.Gluing.trajectory_bound hc v.lower v.upper v.decrease z w hz hrec k

/-- Assemble the manuscript's finite-horizon argument from its stated,
independently checkable ingredients. -/
theorem finite_horizon_certificate {T S : W → E → E} {C : Set E} {P : E → ℝ}
    {c Λ : ℝ} {N : ℕ}
    (hc : 0 ≤ c) (hΛ : 1 ≤ Λ) (hN : 1 < N)
    (hCscale : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → t • z ∈ C)
    (hS : ∀ w z, z ∈ C → S w z ∈ C)
    (hscale : ∀ w z, z ∈ C → T w z = c • S w z)
    (hbound : ∀ w z, z ∈ C → ‖S w z‖ ≤ Λ * ‖z‖)
    (hLip : ∀ w x y, x ∈ C → y ∈ C → ‖S w x - S w y‖ ≤ Λ * ‖x-y‖)
    (hhom : ∀ w z, z ∈ C → ∀ t : ℝ, 0 ≤ t → S w (t • z) = t • S w z)
    (hPdec : ∀ w z, z ∈ C → P (S w z) ≤ P z)
    (hPbound : ∀ z ∈ C, P z ≤ ‖z‖)
    (hPhom : ∀ z ∈ C, ∀ t : ℝ, 0 ≤ t → P (t • z) = t * P z)
    (hdelete : ∀ z ∈ C, ∃ z' ∈ C,
      P z' = 0 ∧ ‖z'‖ ≤ ‖z‖ ∧ ‖z-z'‖ ≤ P z)
    (hboundary : ∀ l : List W, l.length = N → ∀ z ∈ C,
      P z = 0 → ‖run S l z‖ ≤ (1/2 : ℝ) * ‖z‖)
    (hregular : ∀ A : ℝ, 1 ≤ A → ∃ J : ℝ, 0 ≤ J ∧
      ∀ x y, x ∈ C → y ∈ C → |Q A P x - Q A P y| ≤ J * ‖x-y‖) :
    ∃ v : Certificate T C c, v.value = V S N (2 * Λ^N) P := by
  let A := 2 * Λ^N
  have hN0 : 0 < N := by omega
  have hp : 1 ≤ Λ^N := one_le_pow_of_one_le hΛ N
  have hA : 1 ≤ A := by dsimp [A]; linarith
  obtain ⟨J,hJ,hQ⟩ := hregular A hA
  have hb : ∀ l : List W, l.length = N → ∀ z ∈ C, ‖run S l z‖ ≤ Q A P z := by
    intro l hl z hz
    exact block_le_Q (block_bound (by linarith) hS hLip hboundary hdelete l hl hz)
  refine ⟨{
    value := V S N A P
    prefactor := A
    lipConstant := max J (Λ^N)
    prefactor_ge_one := hA
    lipConstant_nonneg := hJ.trans (le_max_left _ _)
    lower := fun z _ => norm_le_V S N A P z
    upper := fun z hz => V_upper hN0 hΛ hS hbound hPbound hz
    lipschitz := fun x y hx hy => V_lipschitz hN0 hΛ hS hbound hLip hQ hx hy
    homogeneous := fun z hz t ht => V_homogeneous hN0 hΛ hCscale hS hbound hhom hPhom hz ht
    decrease := ?_
  }, rfl⟩
  intro w z hz
  apply unscale_step hc hS hscale
    (fun z hz t ht => V_homogeneous hN0 hΛ hCscale hS hbound hhom hPhom hz ht)
    (fun w z hz => V_step hN hΛ (by linarith) hS hbound hPdec hb w hz) w hz

end BB.Gluing
