import W5.ThetaCompactReplayBulkData42

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell42_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell42 := by
  native_decide

end W5
