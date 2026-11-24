import W5.ThetaCompactReplayBulkData41

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell41_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell41 := by
  native_decide

end W5
