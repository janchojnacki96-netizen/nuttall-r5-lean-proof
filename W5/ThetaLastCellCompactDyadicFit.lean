import W5.ThetaLastCellReplayRow0
import W5.ThetaLastCellReplayRow1
import W5.ThetaLastCellReplayRow2
import W5.ThetaLastCellReplayRow3
import W5.ThetaLastCellReplayRow4

namespace W5

theorem thetaLastCellReplayRowsFit (i : Fin 5) :
    ThetaLastCellReplayRowFits i := by
  fin_cases i
  · exact thetaLastCellReplayRow0_checked
  · exact thetaLastCellReplayRow1_checked
  · exact thetaLastCellReplayRow2_checked
  · exact thetaLastCellReplayRow3_checked
  · exact thetaLastCellReplayRow4_checked

/-- Independent row checks certify the entire small replay matrix.
No evaluation of the original high-denominator matrix is required. -/
theorem thetaLastCellWitnessFits :
    ThetaUpperMatrixRefines thetaLastCellWitness thetaLastCellReplaySource := by
  intro i j hij
  have h := thetaLastCellReplayRowsFit i j hij
  rw [thetaLastCellReplayRowSource_apply i j hij] at h
  exact h

end W5
