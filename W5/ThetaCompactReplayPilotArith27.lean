import W5.ThetaCompactReplayPilotData

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell27_arithmetic :
    ThetaCompactReplayArithmeticFits thetaCompactReplayCell27 := by
  native_decide

end W5
