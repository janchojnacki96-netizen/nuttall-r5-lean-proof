import W5.ThetaBulk48SharpGammaChecker

/-!
# Budgeted numerical pilot for the last original theta x-cell

The previous 48-bin, 16-bisection pilot exhausted a large part of the
available focused CI budget without reporting the expensive width tests.
Before attempting the LDL matrix, use only 12 bins of width four and
8 fourth-root bisections. Concentrate on k=7,8, the largest estimated
sources of fifth-pivot interval uncertainty.

This is ONLY a diagnostic: no #eval is asserted as a theorem and
the original 48-cell numerical Boolean goal remains open.
-/

namespace W5

def thetaGammaPilotGrid : List ℚ :=
  (List.range 12).map (fun j => ((4*(j+1):ℕ):ℚ))

def thetaGammaPilotLastLeft : ℚ :=
  (endpoints.reverse.drop 1).head!
def thetaGammaPilotLastRight : ℚ :=
  endpoints.reverse.head!

-- Check the fully rational root/Gamma/exp eligibility at the right endpoint.
set_option maxHeartbeats 2000000 in
#eval thetaGammaAutoMomentCheck 8 thetaGammaPilotLastRight thetaGammaPilotGrid

-- The exact same original moment, but compare the widths of the
-- NEW rigorously certified finite-grid+infinite-tail enclosure against
-- the old global quadratic/cubic enclosure.
def thetaGammaPilotWidthBetter (k : ℕ) : Bool :=
  let fresh := thetaGammaAutoCellMomentBox
    8 k thetaGammaPilotLastLeft thetaGammaPilotLastRight 1 thetaGammaPilotGrid
  let old := thetaNthCubicGammaMomentBox
    thetaGammaPilotLastLeft thetaGammaPilotLastRight 1 k
  decide (fresh.hi-fresh.lo < old.hi-old.lo)

set_option maxHeartbeats 2000000 in
#eval [thetaGammaPilotWidthBetter 7, thetaGammaPilotWidthBetter 8]

end W5
