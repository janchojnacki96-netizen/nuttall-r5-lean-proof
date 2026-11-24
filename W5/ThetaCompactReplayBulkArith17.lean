import W5.ThetaCompactReplayBulkData17

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell17_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell17 := by
  native_decide

end W5
