import W5.ThetaCompactReplayBulkData26

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell26_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell26 := by
  native_decide

end W5
