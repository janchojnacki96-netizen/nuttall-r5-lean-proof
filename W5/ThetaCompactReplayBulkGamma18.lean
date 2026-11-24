import W5.ThetaCompactReplayBulkData18

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell18_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell18 := by
  native_decide

end W5
