import W5.ThetaLastCellGammaReplayData

namespace W5

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellWExpTable_eq :
    thetaLastCellWExpTable =
      ((0:ℚ) :: thetaLastCellGrid).map (fun t => (t, thetaGammaBinExpNegBox t)) := by
  native_decide

theorem thetaLastCellWExp_eq (t : ℚ) :
    thetaLastCellWExp t = thetaGammaBinExpNegBox t := by
  unfold thetaLastCellWExp
  rw [thetaLastCellWExpTable_eq]
  exact thetaGammaMemoExpLookup_map_eq _ _ _

theorem thetaLastCellGrid_explicit :
    thetaLastCellGrid = ([4,8,12,16,20,24,28,32,36,40,44,48] : List ℚ) := by native_decide

theorem thetaLastCellGrid_last :
    thetaGammaRationalLast 0 thetaLastCellGrid = (48:ℚ) := by native_decide

end W5
