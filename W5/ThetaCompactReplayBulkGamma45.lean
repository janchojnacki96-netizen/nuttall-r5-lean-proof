import W5.ThetaCompactReplayBulkData45

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell45_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell45 := by
  native_decide

end W5
