import W5.ThetaCompactReplayBulkData36

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell36_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell36 := by
  native_decide

end W5
