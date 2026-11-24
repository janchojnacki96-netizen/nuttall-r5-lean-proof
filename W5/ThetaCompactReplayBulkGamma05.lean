import W5.ThetaCompactReplayBulkData05

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell05_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell05 := by
  native_decide

end W5
