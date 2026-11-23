import W5.ThetaBulk48SharpGammaChecker

/-!
# Cheap targeted numerical pilot for the last original theta x-cell

The original last-cell fifth LDL pivot fails even after a 2-way
split (CI #45271639614). Before evaluating the EXPENSIVE full
five-stage LDL matrix with sharp Gamma moments, test whether
the newly certified full-M_k intervals substantially improve
the obsolete global cubic moment bounds.

This is ONLY a diagnostic: no #eval is asserted as a theorem and
the original 48-cell numerical Boolean goal remains open.
-/

namespace W5

def thetaGammaPilotGrid : List ℚ :=
  (List.range 48).map (fun j => ((j+1:ℕ):ℚ))

def thetaGammaPilotLastLeft : ℚ :=
  (endpoints.reverse.drop 1).head!
def thetaGammaPilotLastRight : ℚ :=
  endpoints.reverse.head!

-- Check the fully rational root/Gamma/exp eligibility at the right endpoint.
set_option maxHeartbeats 2000000 in
#eval thetaGammaAutoMomentCheck 16 thetaGammaPilotLastRight thetaGammaPilotGrid

-- The exact same original moment, but compare the widths of the
-- NEW rigorously certified finite-grid+infinite-tail enclosure against
-- the old global quadratic/cubic enclosure.
def thetaGammaPilotWidthBetter (k : ℕ) : Bool :=
  let fresh := thetaGammaAutoCellMomentBox
    16 k thetaGammaPilotLastLeft thetaGammaPilotLastRight 1 thetaGammaPilotGrid
  let old := thetaNthCubicGammaMomentBox
    thetaGammaPilotLastLeft thetaGammaPilotLastRight 1 k
  decide (fresh.hi-fresh.lo < old.hi-old.lo)

set_option maxHeartbeats 2000000 in
#eval [thetaGammaPilotWidthBetter 0,
       thetaGammaPilotWidthBetter 4,
       thetaGammaPilotWidthBetter 8]

end W5
