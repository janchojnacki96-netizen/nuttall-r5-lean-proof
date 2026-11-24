import W5.ThetaLastCellGammaReplayData

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellGammaMomentSums_checked :
    ThetaLastCellGammaMomentSumsFit := by
  native_decide

end W5
