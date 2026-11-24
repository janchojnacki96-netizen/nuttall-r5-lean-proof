import W5.ThetaCompactReplayBulkData30

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell30_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell30 := by
  native_decide

end W5
