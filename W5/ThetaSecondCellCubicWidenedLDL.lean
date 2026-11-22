import W5.ThetaSecondCellCubicFirstSquareMatrix

/-!
# A single SECOND-CELL 5x5 LDL check with a uniform tail allowance

The first-square matrix is a fully computable exact-rational
binomial / cubic-Gamma interval expression. Widen every entry
by the SAME rational [-1/100,1/100], leaving enough room for
all original theta square indices n>=2.

The finite LDL result is proved by the EXISTING 5-step checker.
It is independent of the old 768-bit entrywise audit.
Future analytic lemmas must prove the real n=1 enclosure
and the 1/100 bound on the TRUE n>=2 tail, not merely assert them.
-/

namespace W5

def thetaSecondCellUniformTailAllowance : QInterval :=
  ⟨-1/100, 1/100⟩

/-- One exact rational matrix, including a symmetric one-percent
absolute error allowance for the full n>=2 series. -/
def thetaSecondCellCubicWidenedMatrix : ThetaIntervalMatrix :=
  fun i j =>
    QInterval.add (thetaSecondCellCubicFirstSquareMatrix i j)
      thetaSecondCellUniformTailAllowance

/-- Only a finite rational test; the true theta-series enclosure
remains a separate analytic obligation. -/
theorem thetaSecondCellCubicWidenedMatrix_checked :
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaSecondCellCubicWidenedMatrix) =
        true := by
  native_decide

theorem thetaSecondCellCubicWidenedMatrix_pivotSigns :
    intervalLDL5Alternating
      (thetaSymmetricIntervals thetaSecondCellCubicWidenedMatrix) := by
  exact intervalLDL5Alternating_of_check
    (thetaSymmetricIntervals thetaSecondCellCubicWidenedMatrix)
    thetaSecondCellCubicWidenedMatrix_checked

end W5
