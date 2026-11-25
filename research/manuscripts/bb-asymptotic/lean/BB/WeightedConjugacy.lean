import BB.WeightedRates

/-!
# Complete finite weighted root-factor conjugacy

The boundedness needed by a real-valued limsup is proved from the actual
delayed BB update, and both initial normalization constants are removed
using their proved positivity. This is the full root identity, with no
extra asymptotic boundedness hypothesis.
-/

namespace BB
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weighted_gradient_normalized_rootFactor_eq (lam ψ : ι → ℝ) (a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hlam : ∀ i, a ≤ lam i ∧ lam i ≤ b)
    (hψ : ∀ i, 0 < ψ i) (g : ℕ → ι → ℝ) (hg0 : 0 < energy (g 0))
    (hupdate : ∀ n, g (n+2) = gradientUpdate lam (weightedBB lam ψ (g n)) (g (n+1))) :
    rootFactor (fun n => normDiag (spectralScale ψ (g n)) / normDiag (spectralScale ψ (g 0))) =
      rootFactor (fun n => normDiag (g n) / normDiag (g 0)) := by
  have hbg := weighted_gradient_rootTerm_bounded lam ψ a b ha hab hlam hψ g hg0 hupdate
  have hbS := gradient_rootTerm_bounded lam a b ha hab hlam
    (fun n => spectralScale ψ (g n)) (spectral_scale_energy_pos ψ hψ hg0)
    (weighted_delayed_update_conjugacy lam ψ g (fun i => (hψ i).le) hupdate)
  rw [rootFactor_div_const (fun n => normDiag (spectralScale ψ (g n)))
    (fun _ => norm_diag_nonneg _) hbS (normDiag (spectralScale ψ (g 0)))
    (Real.sqrt_pos.mpr (spectral_scale_energy_pos ψ hψ hg0)),
    rootFactor_div_const (fun n => normDiag (g n)) (fun _ => norm_diag_nonneg _) hbg
      (normDiag (g 0)) (Real.sqrt_pos.mpr hg0)]
  obtain ⟨m,M,hm,hM,hlo,hhi⟩ := positive_weights_bounds ψ hψ
  exact weighted_rootFactor_eq ψ g m M hm hM hlo hhi hbg

end
end BB
