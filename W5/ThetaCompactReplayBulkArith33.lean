import W5.ThetaCompactReplayBulkData33

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell33_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell33 := by
  native_decide

end W5
