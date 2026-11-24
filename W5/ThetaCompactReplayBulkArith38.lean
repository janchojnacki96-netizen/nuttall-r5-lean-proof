import W5.ThetaCompactReplayBulkData38

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell38_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell38 := by
  native_decide

end W5
