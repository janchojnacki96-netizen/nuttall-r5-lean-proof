import W5.ThetaEarlyRoundedBothCellMatrix
import W5.ThetaGammaPilotLastCell
import W5.ThetaAuditedMatrixRefinementReuse

/-!
# Fast one-entry numerical pilot: original last right-half theta A44

The previous source was analytically correct but had huge rational
denominators from unrounded n=2 Gamma polynomial expansions. This
pilot uses the NEW formally sound early 2^768 outward rounding BEFORE
those expansions, and the existing memoized nine selected moments.

A full 15-entry/5-pivot run is expensive and premature. Check only
the most influential (4,4) source against the already certified
768-bit audited last-cell target. Both rational inclusion predicates
must return true before any extension to additional coefficients.
The #eval outputs are exploratory, never assumed as a theorem.
-/

namespace W5

def thetaEarlyRoundedLastRightMid : ℚ :=
  (thetaGammaPilotLastLeft + thetaGammaPilotLastRight) / 2

def thetaEarlyRoundedLastK : Finset ℕ := Finset.range 9

def thetaEarlyRoundedLastRightA44Report : List Bool × List ℤ :=
  let A := thetaAuditUpperCell_51 (4 : Fin 5) (4 : Fin 5)
  let B := thetaEarlyRoundedBothCellMatrix
    8 thetaGammaPilotGrid thetaEarlyRoundedLastK
    thetaEarlyRoundedLastRightMid thetaGammaPilotLastRight
    (4 : Fin 5) (4 : Fin 5)
  ([decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)],
   [(A.lo * 1000000).floor, (A.hi * 1000000).floor,
    (B.lo * 1000000).floor, (B.hi * 1000000).floor])

/-- Independently check the analytic assumptions of the
already-proved real-enclosure theorem on this subcell. -/
set_option maxHeartbeats 3000000 in
#eval [thetaGammaAutoMomentCheck
        8 thetaEarlyRoundedLastRightMid thetaGammaPilotGrid,
       thetaGammaAutoMomentCheck
        8 thetaGammaPilotLastRight thetaGammaPilotGrid,
       decide (ThetaBulkGaussianEligibility
         thetaEarlyRoundedLastRightMid thetaGammaPilotLastRight),
       decide (ThetaBulkSelectedGammaEligibility
         8 thetaGammaPilotGrid ({2} : Finset ℕ)
         thetaEarlyRoundedLastRightMid thetaGammaPilotLastRight)]

-- One coefficient only. Failures here must not be promoted to
-- original analytic positivity or a hypothetical Nuttall result.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
#eval thetaEarlyRoundedLastRightA44Report

end W5
