import W5.ThetaDirectMaterializedLDL

/-!
# Direct LDL pilot on the same right half of cell 51 as PR #198

Use identical Gamma settings for a controlled comparison:
12 w-bins of width 4, eight root bisections, all nine moment orders.
Unlike #198, never consult the imported target audit matrix.
The diagnostic reports the first pivot failing its required sign,
or all five successful signs, with rational interval endpoints
rounded outward to millionths for readable logs only.
-/

namespace W5

def thetaDirectPilotGrid : List ℚ :=
  (List.range 12).map (fun j => ((4*(j+1):ℕ):ℚ))

def thetaDirectPilotRight : ℚ := endpoints.reverse.head!
def thetaDirectPilotLeft : ℚ :=
  ((endpoints.reverse.drop 1).head! + thetaDirectPilotRight) / 2

/-- Short-circuit after the first unseparated pivot. Later Schur
steps would otherwise be uninformative. No floating point is used. -/
def thetaDirectPilotPivotReport (B : ThetaIntervalMatrix) :
    ℕ → ℕ → List (ℕ × Bool × ℤ × ℤ)
  | _, 0 => []
  | k, fuel+1 =>
      let p := B (pivotIndexFive k) (pivotIndexFive k)
      let ok := if k % 2 = 0 then decide (0 < p.lo)
        else decide (p.hi < 0)
      let row := (k+1, ok, (p.lo*1000000).floor, (p.hi*1000000).ceil)
      if ok then row :: thetaDirectPilotPivotReport
        (thetaDirectCacheMatrix (intervalSchurStep B (pivotIndexFive k)))
        (k+1) fuel
      else [row]

def thetaDirectLastCellReport : Option (List (ℕ × Bool × ℤ × ℤ)) :=
  if thetaRunningCellEligible 8 thetaDirectPilotGrid
      thetaDirectPilotLeft thetaDirectPilotRight then
    let B := thetaDirectCacheMatrix (thetaSymmetricIntervals
      (thetaRunningMaterializedBothCellMatrix 8 thetaDirectPilotGrid
        (Finset.range 9) thetaDirectPilotLeft thetaDirectPilotRight))
    some (thetaDirectPilotPivotReport B 0 5)
  else none

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
#eval thetaDirectLastCellReport

end W5
