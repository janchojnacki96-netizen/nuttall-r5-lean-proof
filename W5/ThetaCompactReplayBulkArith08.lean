import W5.ThetaCompactReplayBulkData08

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell08_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell08 := by
  native_decide

end W5
