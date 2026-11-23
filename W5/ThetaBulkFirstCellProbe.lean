import W5.ThetaBulk48GeneratedVerifier

/-!
# Boundary cell diagnostic for the common 48-cell sound Boolean checker

The FIRST residual x-cell has already evaluated to true (CI #45248490166).
This probe now checks the LAST, potentially hardest, x-cell directly.
It is a diagnostic and is NOT imported by W5.lean; a full 48-cell
certificate still requires a proof of the combined Boolean equality.
-/

namespace W5

/-- The exact final audited endpoints, read from the existing 51-cell table. -/
def thetaBulkLastCellLeft : ℚ := (endpoints.reverse.drop 1).head!
def thetaBulkLastCellRight : ℚ := endpoints.reverse.head!

-- Does the Gaussian Taylor65 generator meet its range/positivity conditions?
#eval decide (ThetaBulkGaussianEligibility
  thetaBulkLastCellLeft thetaBulkLastCellRight)

-- If eligible, are all 5 original-theta rational LDL pivot signs certified?
#eval thetaBulk48GeneratedCheck thetaBulkLastCellLeft [thetaBulkLastCellRight]

end W5
