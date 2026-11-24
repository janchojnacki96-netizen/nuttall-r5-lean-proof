import W5.ThetaCompactReplayBulkData10

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell10_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell10 := by
  native_decide

end W5
