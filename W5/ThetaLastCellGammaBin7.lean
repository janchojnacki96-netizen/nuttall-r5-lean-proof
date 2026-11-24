import W5.ThetaLastCellGammaReplayData

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellGammaBin7_checked :
    ThetaLastCellGammaBinFits (7:Fin 12) := by
  native_decide

end W5
