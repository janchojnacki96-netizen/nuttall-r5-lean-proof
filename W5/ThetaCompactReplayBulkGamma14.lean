import W5.ThetaCompactReplayBulkData14

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell14_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell14 := by
  native_decide

end W5
