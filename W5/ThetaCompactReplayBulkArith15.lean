import W5.ThetaCompactReplayBulkData15

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell15_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell15 := by
  native_decide

end W5
