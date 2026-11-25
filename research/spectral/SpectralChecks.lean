import Mathlib

namespace SpectralReadingNote

/-- The two multipliers for a reciprocal step equal to the endpoint midpoint. -/
theorem midpointMultipliers (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    1 - a / ((a + b) / 2) = (b - a) / (b + a) ∧
    1 - b / ((a + b) / 2) = - ((b - a) / (b + a)) := by
  have h : 0 < a + b := by linarith
  have h' : 0 < b + a := by linarith
  constructor <;> field_simp <;> ring

/-- Two equal nonzero endpoint energies give the midpoint Rayleigh quotient. -/
theorem balancedRayleigh (a b s : ℝ) (hs : 0 < s) :
    (a * s + b * s) / (s + s) = (a + b) / 2 := by
  have h : s + s ≠ 0 := by linarith
  field_simp
  ring

/-- Cauchy–Binet for a diagonal form on three coordinates compressed to two. -/
theorem determinantExpansion32 (x₁ y₁ x₂ y₂ x₃ y₃ d₁ d₂ d₃ : ℝ) :
    (d₁*x₁^2 + d₂*x₂^2 + d₃*x₃^2) * (d₁*y₁^2 + d₂*y₂^2 + d₃*y₃^2) -
      (d₁*x₁*y₁ + d₂*x₂*y₂ + d₃*x₃*y₃)^2 =
    d₁*d₂*(x₁*y₂ - x₂*y₁)^2 +
      d₁*d₃*(x₁*y₃ - x₃*y₁)^2 +
      d₂*d₃*(x₂*y₃ - x₃*y₂)^2 := by ring

end SpectralReadingNote

#print axioms SpectralReadingNote.midpointMultipliers
#print axioms SpectralReadingNote.balancedRayleigh
#print axioms SpectralReadingNote.determinantExpansion32
