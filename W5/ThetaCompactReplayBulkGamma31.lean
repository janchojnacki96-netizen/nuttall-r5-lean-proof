import W5.ThetaCompactReplayBulkData31

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell31_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell31 := by
  native_decide

end W5
