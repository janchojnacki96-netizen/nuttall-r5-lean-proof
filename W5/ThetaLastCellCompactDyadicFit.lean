import W5.ThetaLastCellReplayRow0
import W5.ThetaLastCellReplayRow1
import W5.ThetaLastCellReplayRow2
import W5.ThetaLastCellReplayRow3
import W5.ThetaLastCellReplayRow4

namespace W5

/-- Enumerate only abstract propositions. Running fin_cases on the
concrete interval goal lets simp/defeq expand a certified matrix again. -/
private theorem thetaLastCellFin5Cases (P : Fin 5 → Prop)
    (h0 : P 0) (h1 : P 1) (h2 : P 2) (h3 : P 3) (h4 : P 4) :
    ∀ i : Fin 5, P i := by
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

-- Keep the checked computational objects symbolic in this proof-only module.
local attribute [irreducible] thetaLastCellWitness thetaLastCellReplaySource
  thetaLastCellReplayRowSource

theorem thetaLastCellReplayRowsFit (i : Fin 5) :
    ThetaLastCellReplayRowFits i :=
  thetaLastCellFin5Cases ThetaLastCellReplayRowFits
    thetaLastCellReplayRow0_checked thetaLastCellReplayRow1_checked
    thetaLastCellReplayRow2_checked thetaLastCellReplayRow3_checked
    thetaLastCellReplayRow4_checked i

/-- Pure logical transport of the independently verified rows. -/
theorem thetaLastCellWitnessFits :
    ThetaUpperMatrixRefines thetaLastCellWitness thetaLastCellReplaySource := by
  intro i j hij
  have h : (thetaLastCellWitness i j).lo ≤ (thetaLastCellReplayRowSource i j).lo ∧
      (thetaLastCellReplayRowSource i j).hi ≤ (thetaLastCellWitness i j).hi :=
    thetaLastCellReplayRowsFit i j hij
  simpa only [thetaLastCellReplayRowSource_apply i j hij] using h

end W5
