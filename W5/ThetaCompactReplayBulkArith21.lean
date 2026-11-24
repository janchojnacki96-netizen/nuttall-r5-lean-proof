import W5.ThetaCompactReplayBulkData21

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell21_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell21 := by
  native_decide

end W5
