import W5.ThetaRunningMaterializedNine

namespace W5

def thetaMaterializedPilotGrid : List ℚ :=
  (List.range 12).map (fun j => ((4*(j+1):ℕ):ℚ))

def thetaMaterializedPilotRight : ℚ := endpoints.reverse.head!
def thetaMaterializedPilotLeft : ℚ :=
  ((endpoints.reverse.drop 1).head! + thetaMaterializedPilotRight) / 2

/-- Report containment of A44 and A34 before any direct LDL calculation.
The original target has already passed all five audited rational pivots.
All values printed in millionths are diagnostic only. -/
def thetaMaterializedPilotEntryReport : List Bool × List ℤ :=
  let source := thetaRunningMaterializedBothCellMatrix
    8 thetaMaterializedPilotGrid (Finset.range 9)
    thetaMaterializedPilotLeft thetaMaterializedPilotRight
  let A := thetaAuditUpperCell_51
  let b44 := source 4 4
  let b34 := source 3 4
  let a44 := A 4 4
  let a34 := A 3 4
  ([decide (a44.lo ≤ b44.lo), decide (b44.hi ≤ a44.hi),
    decide (a34.lo ≤ b34.lo), decide (b34.hi ≤ a34.hi)],
   [ (a44.lo * 1000000).floor, (a44.hi * 1000000).floor,
     (b44.lo * 1000000).floor, (b44.hi * 1000000).floor,
     (a34.lo * 1000000).floor, (a34.hi * 1000000).floor,
     (b34.lo * 1000000).floor, (b34.hi * 1000000).floor ])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
#eval thetaRunningCellEligible 8 thetaMaterializedPilotGrid
  thetaMaterializedPilotLeft thetaMaterializedPilotRight

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
#eval thetaMaterializedPilotEntryReport

end W5
