import W5.ThetaCompactReplayBulkData25

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell25_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell25 := by
  native_decide

end W5
