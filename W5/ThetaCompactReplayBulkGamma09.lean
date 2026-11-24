import W5.ThetaCompactReplayBulkData09

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell09_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell09 := by
  native_decide

end W5
