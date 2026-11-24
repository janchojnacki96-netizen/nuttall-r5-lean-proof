import W5.ThetaCompactReplayBulkData43

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell43_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell43 := by
  native_decide

end W5
