import W5.ThetaCompactReplayBulkData12

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell12_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell12 := by
  native_decide

end W5
