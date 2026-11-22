import W5.ThetaAuditedMomentGammaCubicCellBox

/-!
# Second-cell full-matrix finite candidate from binomial/Gamma bounds

A fully COMPUTABLE rational evaluator for the original n=1
coefficient polynomial. Its formula is exactly the already-proved
thetaFirstCell_original_coeff_binomial specialized to rationals:
no noncomputable nested-polynomial multiplication is needed.

This independent finite CHECK of alternating LDL pivot signs uses
the existing original intervalLDL5AlternatingCheck, rather than
new determinant arithmetic or 768-bit data.

Only the n=1 finite candidate is checked here. A later soundness
bridge must identify this rational evaluator with the TRUE real
original theta coefficients, and a separate bound must include the
n>=2 infinite tail. Thus the finite check alone is NOT an R5 proof.
-/

namespace W5

/-- Computable rational binomial coefficient box for the true
n=1 weighted-polynomial coefficient on the second x-cell. -/
def thetaSecondCellCubicBinomialCoefficientBox
    (i j : Fin 5) (k : ℕ) : QInterval :=
  QInterval.finsetSum (Finset.range (min i.val j.val + 1))
    (fun t =>
      let m : ℕ := i.val+j.val-2*t
      let u : ℕ := k-m
      if m ≤ k then
        QInterval.mul
          (QInterval.point
            (((-1:ℚ)^(i.val+j.val-t)) /
              ((Nat.factorial t : ℚ) *
               (Nat.factorial (i.val-t) : ℚ) *
               (Nat.factorial (j.val-t) : ℚ)) *
               (t.choose u : ℚ)))
          (QInterval.pow (⟨1/8,177/512⟩ : QInterval) (m+2*u))
      else QInterval.point 0)

/-- Entire n=1 interval matrix (no higher square indices).
Cubic Gamma moments are reused for every k and all 25 entries. -/
def thetaSecondCellCubicFirstSquareMatrix : ThetaIntervalMatrix :=
  fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox (1/8) (177/512))
      (thetaSecondCellCubicBinomialCoefficientBox i j)
      (thetaNthCubicGammaMomentBox (1/8) (177/512) 1) 9

/-- Exact finite rational LDL check. Real/analytic enclosure
of the original full coefficient series is a SEPARATE obligation. -/
theorem thetaSecondCellCubicFirstSquareMatrix_checked :
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaSecondCellCubicFirstSquareMatrix) =
        true := by
  native_decide

theorem thetaSecondCellCubicFirstSquareMatrix_pivotSigns :
    intervalLDL5Alternating
      (thetaSymmetricIntervals thetaSecondCellCubicFirstSquareMatrix) := by
  exact intervalLDL5Alternating_of_check
    (thetaSymmetricIntervals thetaSecondCellCubicFirstSquareMatrix)
    thetaSecondCellCubicFirstSquareMatrix_checked

end W5
