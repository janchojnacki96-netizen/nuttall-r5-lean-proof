import W5.ThetaCompactReplayBulkData34

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell34_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell34 := by
  native_decide

end W5
