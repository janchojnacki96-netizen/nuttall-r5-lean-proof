import W5.ThetaLastCellCompactDyadicBase

namespace W5

/-- No #eval, no huge-denominator Schur calculation on the source:
only an exact native interval inclusion computation remains. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellWitnessFits :
    thetaUpperMatrixRefinesCheck thetaLastCellWitness thetaLastCellCachedUpperSource = true := by
  native_decide

end W5
