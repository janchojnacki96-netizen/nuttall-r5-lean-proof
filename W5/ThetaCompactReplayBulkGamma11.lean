import W5.ThetaCompactReplayBulkData11

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell11_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell11 := by
  native_decide

end W5
