import W5.ThetaLastCellCompactDyadicBase

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellWitnessLDL :
    intervalLDL5AlternatingCheck (thetaSymmetricIntervals thetaLastCellWitness) = true := by
  rw [← thetaDirectLDLCheck_eq]
  native_decide

end W5
