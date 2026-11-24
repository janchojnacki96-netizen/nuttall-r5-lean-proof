import W5.ThetaCompactReplayBulkData13

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell13_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell13 := by
  native_decide

end W5
