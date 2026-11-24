import W5.ThetaMemoN1N2SelectedCellMatrix
import W5.ThetaGammaPilotLastCell
import W5.ThetaAuditedMatrixRefinementReuse

/-!
# Last-cell right-half original-theta interval inclusion experiment

Evaluate the CERTIFIED exact-rational source matrix using the now
shared n=1 nine-moment cache (K=0..8) and n=2 nine-moment cache.
The same original n=3..6 terms and n>=7 tail are retained.
The old 768-bit audit target is not modified.

Only the two entries (4,4) and (3,4) are evaluated first, to avoid
spending another 15-entry computation on an unsuccessful pilot.
Boolean inclusion comparisons use exact rational arithmetic, while
readable numerical coordinates are merely floored micro-units.
No #eval Boolean is assumed true by a theorem.
-/

namespace W5

def thetaMemoBothLastMid : ℚ :=
  (thetaGammaPilotLastLeft + thetaGammaPilotLastRight) / 2

/-- For nine moments, the full selected set is almost free once
the array is computed once per n and original x-cell. -/
def thetaMemoBothLastK : Finset ℕ := Finset.range 9

def thetaMemoBothRightHalfSource : ThetaIntervalMatrix :=
  thetaMemoN1N2SelectedCellMatrix
    8 thetaGammaPilotGrid thetaMemoBothLastK
    thetaMemoBothLastMid thetaGammaPilotLastRight

def thetaMemoBothRightHalfReport (i j : Fin 5) :
    List Bool × List ℤ :=
  let A := thetaAuditUpperCell_51 i j
  let B := thetaMemoBothRightHalfSource i j
  ([decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)],
   [(A.lo * 1000000).floor, (A.hi * 1000000).floor,
    (B.lo * 1000000).floor, (B.hi * 1000000).floor])

-- All four required conditions for this real-sound source are
-- independently computable and must be verified before promoting it.
set_option maxHeartbeats 3000000 in
#eval [thetaGammaAutoMomentCheck
         8 thetaMemoBothLastMid thetaGammaPilotGrid,
       thetaGammaAutoMomentCheck
         8 thetaGammaPilotLastRight thetaGammaPilotGrid,
       decide (ThetaBulkGaussianEligibility
         thetaMemoBothLastMid thetaGammaPilotLastRight),
       decide (ThetaBulkSelectedGammaEligibility
         8 thetaGammaPilotGrid ({2} : Finset ℕ)
         thetaMemoBothLastMid thetaGammaPilotLastRight)]

-- The two highest-impact ORIGINAL matrix entries. The sign
-- and all 51-cell certificates remain open if either Boolean fails.
set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
#eval [thetaMemoBothRightHalfReport 4 4,
       thetaMemoBothRightHalfReport 3 4]

end W5
