import W5.ThetaLastCellReplayInputs

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellReplayRow2_checked : ThetaLastCellReplayRowFits (2:Fin 5) := by
  native_decide

end W5
