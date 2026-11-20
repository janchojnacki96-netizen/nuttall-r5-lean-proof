import W5.ThetaAuditedFirstCellFinitePivotCheck

/-!
# Evaluate ALL 255 real-theta-certificate rational pivot inequalities in Lean

The original 768-bit integer auditor exported 51 explicit interval matrices.
Every one of these is imported as EXACT rational endpoints, with the
actual 5×5 matrices reconstructed using the verified theta symmetry.

The signed interval LDL update and its soundness are already proved.
This module asks Lean to evaluate the SAME five-pivot Boolean checker
on all 51 imported matrices in one closed finite computation, reusing
Mathlib's list traversal and native decision procedure.

IMPORTANT: This is a proof only of the finite rational inequalities
for these explicitly imported matrices. It does NOT yet certify that
their entries enclose the transcendental thetaCoefficient values on
their respective x-ranges, and cannot prove W5.MainClaim by itself.
-/

namespace W5

/-- Exactly 51 × 5 finite pivot tests on the original 768-bit
integer interval endpoints, with no numerical tolerance or heuristic. -/
def thetaAuditAll51PivotTests : Bool :=
  thetaAuditCellMatrices.all intervalLDL5AlternatingCheck

/-- The complete finite 255-pivot sign computation, with the values
of all 51 matrices exposed as literal Lean data definitions. -/
theorem thetaAuditAll51PivotTests_true :
    thetaAuditAll51PivotTests = true := by
  native_decide

end W5
