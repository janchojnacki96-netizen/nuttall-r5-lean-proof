import W5.ThetaCompactReplayBulkData44

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell44_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell44 := by
  native_decide

end W5
