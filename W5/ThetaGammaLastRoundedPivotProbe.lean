import W5.ThetaBulkRoundedDegreeSelectedCells
import W5.ThetaGammaPilotLastCell

/-!
# Budgeted exact-rational last-cell LDL diagnostic

Reuse the existing CI-confirmed 12-bin / 8-bisection Gamma pilot and
select only k=7,8 from the n=1 weighted moments. All n=2,...,6
remain in the previously certified cubic-Gamma mode.

Before LDL all 25 true coefficient enclosures are rounded OUTWARD
to the existing audited 2^768 scale (proved in the imported module).
This controls the denominator size without assuming any numerical sign.

The five checks below are only #eval diagnostics, NOT the final
native_decide theorem; report all five explicitly so a false fifth
pivot cannot be mistaken for a counterexample or a proof.
-/

namespace W5

/-- The two moment degrees identified as the most expensive
uncertainty sources in the original last x-cell. -/
def thetaGammaLastProbeDegrees : Finset ℕ := {7, 8}

/-- Exactly the TRUE last-cell rational matrix built from the
new verified selected-moment generator and outward rounding. -/
def thetaGammaLastRoundedSelectedMatrix :
    Matrix (Fin 5) (Fin 5) QInterval :=
  thetaSymmetricIntervals
    (thetaBulkRoundedDegreeSelectedCellMatrix
      8 thetaGammaPilotGrid thetaGammaLastProbeDegrees
      ∅ thetaGammaPilotLastLeft thetaGammaPilotLastRight)

/-- Execute the same five signed Schur steps as intervalLDL5,
but memoize intermediate matrices once during diagnostic evaluation.
The values are *only diagnostic* until a separate Boolean checker
is proved true using its established soundness theorem. -/
/-- Cache each of the 25 entries ONCE using a fixed 5x5 array.
A Matrix is a function, so naively evaluating five nested Schur
updates repeatedly recomputes expensive Gamma integrals. This
helper is used only for an #eval diagnostic, never as a proof step. -/
def thetaGammaMemoMatrix
    (B : Matrix (Fin 5) (Fin 5) QInterval) :
    Matrix (Fin 5) (Fin 5) QInterval :=
  let rows : Array (Array QInterval) :=
    Array.ofFn (fun i : Fin 5 =>
      Array.ofFn (fun j : Fin 5 => B i j))
  fun i j => rows[i.val]![j.val]!

def thetaGammaLastRoundedSelectedPivotBooleans : List Bool :=
  Id.run do
    let mut B := thetaGammaMemoMatrix thetaGammaLastRoundedSelectedMatrix
    let mut checks : List Bool := []
    for k in List.range 5 do
      let i := pivotIndexFive k
      let P := B i i
      let good : Bool :=
        if k % 2 = 0 then decide (0 < P.lo)
        else decide (P.hi < 0)
      checks := checks ++ [good]
      if k < 4 then
        B := thetaGammaMemoMatrix (intervalSchurStep B i)
    return checks

-- All side conditions are independent of the matrix LDL computation.
set_option maxHeartbeats 3000000 in
#eval [thetaGammaAutoMomentCheck
        8 thetaGammaPilotLastLeft thetaGammaPilotGrid,
       thetaGammaAutoMomentCheck
        8 thetaGammaPilotLastRight thetaGammaPilotGrid,
       decide (ThetaBulkGaussianEligibility
         thetaGammaPilotLastLeft thetaGammaPilotLastRight)]

-- The first direct check of all five pivots after targeted k=7,8
-- refinement. A false is diagnostic, not a mathematical counterexample.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
#eval thetaGammaLastRoundedSelectedPivotBooleans

end W5
