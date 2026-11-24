import W5.ThetaCompactReplayBulkData48

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaCompactReplayCell48_gamma :
    ThetaCompactReplayGammaFits thetaCompactReplayCell48 := by
  native_decide

end W5
