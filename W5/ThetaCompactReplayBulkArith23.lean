import W5.ThetaCompactReplayBulkData23

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell23_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell23 := by
  native_decide

end W5
