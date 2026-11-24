import W5.ThetaCompactReplayBulkData32

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell32_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell32 := by
  native_decide

end W5
