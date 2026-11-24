import W5.ThetaGammaFiniteBinIntegral
import W5.VerifiedIntervalRealSemantics
import W5.ThetaAuditedMomentGammaCubicCellBox

/-!
# One certified rational interval for all finite Gamma-bin masses

Instead of numerical quadrature in 48 x-cells, use the exact
Mathlib-certified finite Gamma primitive and two certified exponential
endpoint intervals. Signed interval multiplication and subtraction
are already proved real-sound in W5; no reimplementation is needed.

The result handles all integer moment orders k and all rational
w-bin boundaries L,U with ONE theorem. The remaining numerical work
is just computing tight outward rational exp(-L) and exp(-U) boxes,
which the existing Taylor/rational machinery can generate.
-/

namespace W5

/-- A computable exact-rational enclosure for the incomplete Gamma
mass between two arbitrary rational w-bin endpoints. -/
def thetaGammaBinMassBox (k : ℕ) (L U : ℚ)
    (expL expU : QInterval) : QInterval :=
  QInterval.sub
    (QInterval.mul expL
      (QInterval.point (thetaGammaBinPolyQ k L)))
    (QInterval.mul expU
      (QInterval.point (thetaGammaBinPolyQ k U)))

/-- All finite-bin incomplete Gamma integrals are certified by the
SAME signed interval evaluator and the SAME Mathlib FTC identity.
Neither the theta x-cell nor the numerical size of the w-bin appears
in the proof. -/
theorem thetaGammaBinMassBox_containsReal
    (k : ℕ) (L U : ℚ)
    (expL expU : QInterval)
    (hL : QInterval.ContainsReal expL (Real.exp (-(L:ℝ))))
    (hU : QInterval.ContainsReal expU (Real.exp (-(U:ℝ)))) :
    QInterval.ContainsReal
      (thetaGammaBinMassBox k L U expL expU)
      (∫ w in (L:ℝ)..(U:ℝ), Real.exp (-w) * w^k) := by
  have hpL := thetaRationalPoint_containsReal
    (thetaGammaBinPolyQ k L)
  have hpU := thetaRationalPoint_containsReal
    (thetaGammaBinPolyQ k U)
  have hML := QInterval.mul_containsReal hL hpL
  have hMU := QInterval.mul_containsReal hU hpU
  have hDiff := QInterval.sub_containsReal hML hMU
  rw [thetaGammaBinIntegral_exact]
  simpa only [thetaGammaBinMassBox, thetaGammaBinPolyQ_cast]
    using hDiff

end W5
