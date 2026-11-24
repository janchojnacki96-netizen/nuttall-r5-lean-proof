import W5.ThetaLastCellCompactDyadicBase

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellGammaB_checked :
    thetaGammaAutoMomentCheck 8 thetaLastCellB thetaLastCellGrid = true := by
  native_decide

end W5
