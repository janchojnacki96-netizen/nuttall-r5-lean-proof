import W5.ThetaLastCellReplayInputs

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellReplayGamma2_checked : ThetaLastCellReplayGammaGroupFits (2:Fin 3) := by
  native_decide

end W5
