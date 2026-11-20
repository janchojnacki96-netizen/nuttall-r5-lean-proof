import W5.ThetaAudited768IntervalMatrices
import W5.ThetaFiniteDecidableLDLChecker

/-!
# Concrete exact-rational five-pivot test for the first 768-bit cell

Unlike the earlier conditional sign-transport lemmas, this file
supplies the ACTUAL integer endpoint constants of cell 1 and asks
Lean's native computation tactic to verify the exact five-stage
QInterval Schur checker.

`native_decide` discharges only the FINITE RATIONAL pivot test.
It does NOT prove that the imported endpoints contain the true theta
coefficient values for all 0 < x ≤ 1/8, and does not prove
the full order-five conjecture.
-/

namespace W5

/-- Five actual signed interval pivots for x in the first rational
partition cell, computed from the imported 768-bit endpoint data
using the already proved exact rational LDL checker. -/
theorem thetaAuditCell_01_passes_finite_LDL :
    intervalLDL5Alternating thetaAuditCell_01 := by
  apply intervalLDL5Alternating_of_check
  native_decide

end W5
