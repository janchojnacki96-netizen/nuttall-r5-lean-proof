import W5.ThetaCompactReplayBulkData16

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell16_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell16 := by
  native_decide

end W5
