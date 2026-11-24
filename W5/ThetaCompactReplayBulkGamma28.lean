import W5.ThetaCompactReplayBulkData28

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell28_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell28 := by
  native_decide

end W5
