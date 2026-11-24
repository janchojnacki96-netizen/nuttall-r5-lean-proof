import W5.ThetaCompactReplayBulkData07

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell07_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell07 := by
  native_decide

end W5
