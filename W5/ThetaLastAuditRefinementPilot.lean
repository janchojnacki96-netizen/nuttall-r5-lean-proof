import W5.ThetaAuditedMatrixRefinementReuse
import W5.ThetaBulkDegreeSelectedGammaCells
import W5.ThetaGammaPilotLastCell

/-!
# Cheap last-cell ORIGINAL audit inclusion pilot

Before attempting 51 expensive 5x5 LDL evaluations, test the two
matrix entries that dominate the last fifth-pivot uncertainty:
(4,4) first, (3,4) second. The target intervals are the ORIGINAL
768-bit audit boxes whose pivot signs already passed native_decide.

This uses only the CI-certified real-sound selected Gamma generator,
not any unverified numerical hypothesis. The #eval values are
diagnostics; false merely means the new generated interval is not
yet a refinement of the imported audit box.
-/

namespace W5

/-- Concentrate the expensive certified Gamma grid on those moments
which have the largest first-order influence on the last LDL pivot. -/
def thetaLastAuditPilotDegrees : Finset ℕ := {4, 5, 6, 7, 8}

def thetaLastAuditPilotSource : ThetaIntervalMatrix :=
  thetaBulkDegreeSelectedCellMatrix
    8 thetaGammaPilotGrid thetaLastAuditPilotDegrees ∅
    thetaGammaPilotLastLeft thetaGammaPilotLastRight

/-- Four exact rational inequalities: both sides of the old box. -/
def thetaLastAuditPilotBounds (i j : Fin 5) : List Bool :=
  let A := thetaAuditUpperCell_51 i j
  let B := thetaLastAuditPilotSource i j
  [decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)]

/-- Human-readable integer micro-units, computed from exact rationals.
Order: old lower, old upper, NEW lower, NEW upper. The floor on
each number is only for diagnosis, never for a soundness argument. -/
def thetaLastAuditPilotMicros (i j : Fin 5) : List ℤ :=
  let A := thetaAuditUpperCell_51 i j
  let B := thetaLastAuditPilotSource i j
  [(A.lo * 1000000).floor, (A.hi * 1000000).floor,
   (B.lo * 1000000).floor, (B.hi * 1000000).floor]

/-- Make the four comparisons and four integer coordinates in
one diagnostic pass per entry, without a giant rational printout. -/
def thetaLastAuditPilotReport (i j : Fin 5) :
    List Bool × List ℤ :=
  let A := thetaAuditUpperCell_51 i j
  let B := thetaLastAuditPilotSource i j
  ( [decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)],
    [(A.lo * 1000000).floor, (A.hi * 1000000).floor,
     (B.lo * 1000000).floor, (B.hi * 1000000).floor] )

/-- Separate the cost of the unselected k=0,1,2,3 moments:
integer micro-units of OLD cubic width and NEW certified Gamma width.
These probes are cheaper than recomputing the complete five-pivot LDL. -/
def thetaLastAuditLowMomentWidthMicros (k : ℕ) : List ℤ :=
  let old := thetaNthCubicGammaMomentBox
    thetaGammaPilotLastLeft thetaGammaPilotLastRight 1 k
  let fresh := thetaGammaAutoCellMomentBox
    8 k thetaGammaPilotLastLeft thetaGammaPilotLastRight 1
    thetaGammaPilotGrid
  [((old.hi - old.lo) * 1000000).floor,
   ((fresh.hi - fresh.lo) * 1000000).floor]

/-- In parallel inspect n=2,...,6 term-by-term without recomputing
the expensive selected n=1 Gamma grid. For each term return its
certified rational enclosure width in micro-units. -/
def thetaLastAuditHigherTermWidthMicros (i j : Fin 5) : List ℤ :=
  (List.range 5).map (fun t =>
    let n := t + 2
    let I := thetaBulkDegreeSelectedTermBox
      8 thetaGammaPilotGrid thetaLastAuditPilotDegrees ∅
      thetaGammaPilotLastLeft thetaGammaPilotLastRight i j n
    ((I.hi - I.lo) * 1000000).floor)

/-- Compare the exact-rational original n=2 box against the
existing certified sharp n=2 Gamma generator. Both are sound
provided the checked endpoint eligibility below is true. -/
def thetaLastAuditSharpN2TermWidths (i j : Fin 5) : List ℤ :=
  let O := thetaBulkDegreeSelectedTermBox
    8 thetaGammaPilotGrid thetaLastAuditPilotDegrees ∅
    thetaGammaPilotLastLeft thetaGammaPilotLastRight i j 2
  let N := thetaBulkDegreeSelectedTermBox
    8 thetaGammaPilotGrid thetaLastAuditPilotDegrees
    ({2} : Finset ℕ)
    thetaGammaPilotLastLeft thetaGammaPilotLastRight i j 2
  [((O.hi - O.lo) * 1000000).floor,
   ((N.hi - N.lo) * 1000000).floor,
   (N.lo * 1000000).floor,
   (N.hi * 1000000).floor]

/-- Avoid recomputing the full signed double-binomial n=2 matrix
twice (previous attempt exceeded the CI time budget). Instead
measure the 3 moment degrees most representative of its error
and determine whether sharp n=2 Gamma warrants a cached evaluator. -/
def thetaLastAuditN2MomentWidths (k : ℕ) : List ℤ :=
  let O := thetaNthCubicGammaMomentBox
    thetaGammaPilotLastLeft thetaGammaPilotLastRight 2 k
  let N := thetaGammaAutoCellMomentBox
    8 k thetaGammaPilotLastLeft thetaGammaPilotLastRight
    2 thetaGammaPilotGrid
  [((O.hi - O.lo) * 1000000).floor,
   ((N.hi - N.lo) * 1000000).floor]

set_option maxHeartbeats 3000000 in
#eval decide (ThetaBulkSelectedGammaEligibility
  8 thetaGammaPilotGrid ({2} : Finset ℕ)
  thetaGammaPilotLastLeft thetaGammaPilotLastRight)

/-- The original last x-cell is now split exactly in half.
The signed theta term generator and original 768-bit audit target
remain unchanged; only each source x-range becomes narrower.
The previously proved audited-subgrid theorem allows all five
existing LDL pivot certificates to be reused for both halves. -/
def thetaLastAuditMidpoint : ℚ :=
  (thetaGammaPilotLastLeft + thetaGammaPilotLastRight) / 2

def thetaLastAuditRightHalfSource : ThetaIntervalMatrix :=
  thetaBulkDegreeSelectedCellMatrix
    8 thetaGammaPilotGrid thetaLastAuditPilotDegrees ∅
    thetaLastAuditMidpoint thetaGammaPilotLastRight

/-- Four exact-rational inclusion inequalities and their values
scaled by 10^6; integer printing is ONLY a readable diagnostic. -/
def thetaLastAuditRightHalfReport (i j : Fin 5) :
    List Bool × List ℤ :=
  let A := thetaAuditUpperCell_51 i j
  let B := thetaLastAuditRightHalfSource i j
  ([decide (A.lo ≤ B.lo), decide (B.hi ≤ A.hi)],
   [(A.lo * 1000000).floor, (A.hi * 1000000).floor,
    (B.lo * 1000000).floor, (B.hi * 1000000).floor])

set_option maxHeartbeats 3000000 in
set_option maxRecDepth 4096 in
#eval [thetaLastAuditRightHalfReport 4 4,
       thetaLastAuditRightHalfReport 3 4]

end W5
