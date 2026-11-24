import W5.ThetaGenericAuditedSubgridChecker
import W5.ThetaEarlyRoundedPriorityAuditCheck

/-!
# Single priority-gated certificate for all 48 remaining theta cells

The A44/A34-first numerical gate from the checked priority-audit
module is plugged into the generic, arbitrarily refined 48-cell
real-sound transfer. All original 255 LDL pivot signs are reused.

No cellwise proof duplication. A successful decidable certificate
implies genuine positivity of the original analytic 5x5 matrix.

This is a *conditional* transfer theorem: finite evaluation of the
48-cell Boolean remains a separate, outstanding task.
-/

namespace W5

/-- Check every original remaining audited target on its own
rational subgrid, rejecting on A44/A34 as early as possible. -/
def thetaPriorityAudited48Check
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ)) : Bool :=
  thetaGenericAuditedSubgridsCheck
    (thetaEarlyRoundedPriorityAuditCheck steps us K)
    (821/2048 : ℚ) (endpoints.drop 3)
    (thetaAuditUpperCellMatrices.drop 3) grids

/-- If and only if the supplied exact-rational numerical gate
returns true is the hypothesis discharged; no numerical success
or unproved analytic jet identification is assumed here. -/
theorem analyticMatrixPositive_of_priority_audited48
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ))
    (h : thetaPriorityAudited48Check steps us K grids = true) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_audited_enclosures
  exact thetaGenericAuditedSubgridsCheck_sound
    (thetaEarlyRoundedPriorityAuditCheck steps us K)
    (fun target a b =>
      thetaEarlyRoundedPriorityAuditCheck_sound steps us K target a b)
    (endpoints.drop 3) (821/2048 : ℚ)
    (thetaAuditUpperCellMatrices.drop 3) grids h

end W5
