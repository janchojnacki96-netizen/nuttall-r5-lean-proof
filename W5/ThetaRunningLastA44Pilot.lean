import W5.ThetaRunningOriginalMatrix
import W5.ThetaGammaPilotLastCell

/-!
# Single-entry numerical test of the faster original theta matrix

This reports A44 on only the RIGHT HALF of the last original
audited x-cell. It uses the new per-bin 2^768 outward-running Gamma
moment engine instead of the expensive exact rational sum which was
cancelled after 45 minutes in PR #181. All n=1/n=2 moment degrees
k=0,...,8 remain selected, with the existing n>=3 signed terms and
rigorous n>=7 tail.

The #eval output is an exploratory, non-axiomatic diagnostic. If
the certified right-half A44 source is not included in the original
audited target, the full 48-cell theorem is not instantiated.
-/

namespace W5

def thetaRunningLastRightMid : ℚ :=
  (thetaGammaPilotLastLeft + thetaGammaPilotLastRight) / 2

def thetaRunningLastRightA44Report : List Bool × List ℤ :=
  let A := thetaAuditUpperCell_51 (4 : Fin 5) (4 : Fin 5)
  let B := thetaRunningBothCellMatrix
    8 thetaGammaPilotGrid (Finset.range 9)
    thetaRunningLastRightMid thetaGammaPilotLastRight
    (4 : Fin 5) (4 : Fin 5)
  ([decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)],
   [(A.lo * 1000000).floor, (A.hi * 1000000).floor,
    (B.lo * 1000000).floor, (B.hi * 1000000).floor])

/-- The original exact eligibility conditions, now on the right half.
These cannot substitute for the A44 interval containment itself. -/
set_option maxHeartbeats 3000000 in
#eval [thetaGammaAutoMomentCheck
        8 thetaRunningLastRightMid thetaGammaPilotGrid,
       thetaGammaAutoMomentCheck
        8 thetaGammaPilotLastRight thetaGammaPilotGrid,
       decide (ThetaBulkGaussianEligibility
         thetaRunningLastRightMid thetaGammaPilotLastRight),
       decide (ThetaBulkSelectedGammaEligibility
         8 thetaGammaPilotGrid ({2} : Finset ℕ)
         thetaRunningLastRightMid thetaGammaPilotLastRight)]

-- Single coefficient, not the entire 25-entry matrix or LDL run.
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
#eval thetaRunningLastRightA44Report

end W5
