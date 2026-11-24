import W5.ThetaLastCellGammaReplayData

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellGammaBin4_checked :
    ThetaLastCellGammaBinFits (4:Fin 12) := by
  native_decide

end W5
