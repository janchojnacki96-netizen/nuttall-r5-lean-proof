import W5.ThetaCompactReplayBulkData40

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell40_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell40 := by
  native_decide

end W5
