import Lean.Data.Rat

open Lean

namespace CurvatureQueryChecks

def firstResidual : Rat := 3 - 3 * 3 / (3 + 4)
def secondResidual : Rat := 4 - 4 * 4 / (3 + 4)
def residualCoupling : Rat := -(3 * 4) / (3 + 4)

theorem old_transcript_schur_endpoints :
    (1 : Rat) + 1 / (3 - 1) = 3 / 2 ∧
    (5 : Rat) - 1 / (5 - 3) = 9 / 2 := by decide

theorem oblique_residual_entries :
    firstResidual = 12 / 7 ∧ secondResidual = 12 / 7 ∧
    residualCoupling = -(12 / 7) := by decide

theorem oblique_reply_is_shared :
    firstResidual + residualCoupling = 0 ∧
    residualCoupling + secondResidual = 0 := by decide

theorem oblique_residual_determinant :
    firstResidual * secondResidual - residualCoupling * residualCoupling = 0 := by decide

theorem sum_prefers_second_coordinate :
    (3 : Rat) < firstResidual + secondResidual ∧
    firstResidual + secondResidual = 24 / 7 ∧
    firstResidual + secondResidual < 4 := by decide

theorem maximum_prefers_balanced_residual :
    (3 : Rat) * (1 - 3 / 7) = 4 * (3 / 7) ∧
    (4 : Rat) * (3 / 7) = 12 / 7 ∧
    (12 / 7 : Rat) < 3 := by decide

theorem saturated_reply_determines_missing_curvature :
    (1 : Rat) + 2 * 2 / (3 - 1) = 3 ∧
    (5 : Rat) - 2 * 2 / (5 - 3) = 3 := by decide

#print axioms old_transcript_schur_endpoints
#print axioms oblique_residual_entries
#print axioms oblique_reply_is_shared
#print axioms oblique_residual_determinant
#print axioms sum_prefers_second_coordinate
#print axioms maximum_prefers_balanced_residual
#print axioms saturated_reply_determines_missing_curvature

end CurvatureQueryChecks
