import W5.ThetaCompactReplayBulkData19

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell19_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell19 := by
  native_decide

end W5
