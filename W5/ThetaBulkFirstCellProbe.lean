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
/-- The actual generated 5-by-5 rational interval matrix at the last cell. -/
def thetaBulkLastCellMatrix : Matrix (Fin 5) (Fin 5) QInterval :=
  thetaSymmetricIntervals
    (thetaBulkSevenCellMatrix thetaBulkGeneratedSignedTerm
      thetaBulkLastCellLeft thetaBulkLastCellRight)

-- Diagnose EACH exact pivot separately. This identifies where
-- the interval width prevents a proof rather than retrying 48 cells.
-- Giving the large expression a named Boolean value avoids expensive
-- elaborator reduction of the full matrix during #eval's type inference.
-- Higher heartbeat budget affects only this diagnostic, not proof soundness.
set_option maxHeartbeats 2000000 in
def thetaBulkLastCellPivotChecks : List Bool :=
  let B : Matrix (Fin 5) (Fin 5) QInterval := thetaBulkLastCellMatrix
  [
    decide (0 < ((intervalLDL5 B 0)
      (pivotIndexFive 0) (pivotIndexFive 0)).lo),
    decide (((intervalLDL5 B 1)
      (pivotIndexFive 1) (pivotIndexFive 1)).hi < 0),
    decide (0 < ((intervalLDL5 B 2)
      (pivotIndexFive 2) (pivotIndexFive 2)).lo),
    decide (((intervalLDL5 B 3)
      (pivotIndexFive 3) (pivotIndexFive 3)).hi < 0),
    decide (0 < ((intervalLDL5 B 4)
      (pivotIndexFive 4) (pivotIndexFive 4)).lo)
  ]

#eval thetaBulkLastCellPivotChecks

end W5
