import W5.ThetaCompactReplayBulkData37

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell37_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell37 := by
  native_decide

end W5
