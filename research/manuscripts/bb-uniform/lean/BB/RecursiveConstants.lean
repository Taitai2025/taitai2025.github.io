import BB.BoundaryExplicit
import BB.SpectralFaces

set_option autoImplicit false

noncomputable section
namespace BB.Recursive

/-- Extend a finite ordered spectrum only to make the numerical recursion total.
All certified faces below use indices inside the original finite spectrum. -/
def extend {n : ℕ} (lam : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : i < n then lam ⟨i,h⟩ else 0

@[simp] theorem extend_fin {n : ℕ} (lam : Fin n → ℝ) (i : Fin n) :
    extend lam i.val = lam i := by simp [extend,i.isLt]

def rate (lam : ℕ → ℝ) (lo span : ℕ) : ℝ :=
  BB.endpointRate (lam lo) (lam (lo+span))

/-- The literal recursive pair `(N,K)` in equations (N_recursive) and
(K_recursive). `span=1` means two distinct eigenvalues. The singleton entry is
unused by the rate induction and is set to `(0,1)` only to totalize the function.
The same ambient constants `B,L` are used at every recursive face, as in the text. -/
def constants (lam : ℕ → ℝ) (B L : ℝ) : ℕ → ℕ → ℕ × ℝ
  | 0, _ => (0,1)
  | span+1, lo =>
    let c := rate lam lo (span+1)
    let N := if span = 0 then 3 else
      BB.BoundaryExplicit.length B
        (max (constants lam B L span (lo+1)).2 (constants lam B L span lo).2) c
        (max (rate lam (lo+1) span) (rate lam lo span)/c)
    (N,2*(L/c)^N)

def length (lam : ℕ → ℝ) (B L : ℝ) (lo span : ℕ) : ℕ :=
  (constants lam B L span lo).1

def prefactor (lam : ℕ → ℝ) (B L : ℝ) (lo span : ℕ) : ℝ :=
  (constants lam B L span lo).2

@[simp] theorem length_one (lam : ℕ → ℝ) (B L : ℝ) (lo : ℕ) :
    length lam B L lo 1 = 3 := by simp [length,constants]

@[simp] theorem prefactor_one (lam : ℕ → ℝ) (B L : ℝ) (lo : ℕ) :
    prefactor lam B L lo 1 = 2*(L/rate lam lo 1)^3 := by simp [prefactor,constants]

theorem length_succ_succ (lam : ℕ → ℝ) (B L : ℝ) (lo span : ℕ) :
    length lam B L lo (span+2) =
      BB.BoundaryExplicit.length B
        (max (prefactor lam B L (lo+1) (span+1)) (prefactor lam B L lo (span+1)))
        (rate lam lo (span+2))
        (max (rate lam (lo+1) (span+1)) (rate lam lo (span+1))/rate lam lo (span+2)) := by
  simp only [length,prefactor,constants,Nat.add_eq_zero_iff,Nat.add_one_ne_zero,
    and_false,ite_false]

theorem prefactor_eq (lam : ℕ → ℝ) (B L : ℝ) (lo span : ℕ) (hspan : 0 < span) :
    prefactor lam B L lo span = 2*(L/rate lam lo span)^(length lam B L lo span) := by
  cases span with
  | zero => omega
  | succ span => rfl

theorem length_ge_three (lam : ℕ → ℝ) (B L : ℝ) (lo span : ℕ) (hspan : 0 < span) :
    3 ≤ length lam B L lo span := by
  rcases span with _ | _ | span
  · omega
  · rw [length_one]
  · rw [length_succ_succ]
    exact BB.BoundaryExplicit.length_ge_three _ _ _ _

theorem prefactor_ge_one (lam : ℕ → ℝ) (B L : ℝ) (lo span : ℕ) (hspan : 0 < span)
    (hc : 0 < rate lam lo span) (hcL : rate lam lo span ≤ L) :
    1 ≤ prefactor lam B L lo span := by
  rw [prefactor_eq lam B L lo span hspan]
  have hpow := one_le_pow_of_one_le ((one_le_div hc).mpr hcL) (length lam B L lo span)
  linarith only [hpow]

/-- The exact recursive horizon controls the boundary handoff term using its
two recursively obtained child prefactors, without replacing either by another
existential constant. -/
theorem recursive_boundary_half (lam : ℕ → ℝ) {B L : ℝ} (lo span : ℕ)
    (hB : 0 < B) (hc : 0 < rate lam lo (span+2))
    (hminus : 0 < rate lam (lo+1) (span+1))
    (hplus : 0 < rate lam lo (span+1))
    (hminuslt : rate lam (lo+1) (span+1) < rate lam lo (span+2))
    (hpluslt : rate lam lo (span+1) < rate lam lo (span+2))
    (hKm : 0 < prefactor lam B L (lo+1) (span+1))
    (hKp : 0 < prefactor lam B L lo (span+1)) :
    (B/rate lam lo (span+2))*
      max (prefactor lam B L (lo+1) (span+1)) (prefactor lam B L lo (span+1)) *
      (max (rate lam (lo+1) (span+1)) (rate lam lo (span+1))/rate lam lo (span+2))^
        (length lam B L lo (span+2)-1) ≤ 1/2 := by
  rw [length_succ_succ]
  exact BB.BoundaryExplicit.boundary_length_half hB (hKm.trans_le (le_max_left _ _)) hc
    (div_pos (hminus.trans_le (le_max_left _ _)) hc)
    ((div_lt_one hc).mpr (max_lt hminuslt hpluslt))

end BB.Recursive
