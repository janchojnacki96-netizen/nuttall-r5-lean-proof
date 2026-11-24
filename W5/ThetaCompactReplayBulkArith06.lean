import W5.ThetaCompactReplayBulkData06

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell06_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell06 := by
  native_decide

end W5
