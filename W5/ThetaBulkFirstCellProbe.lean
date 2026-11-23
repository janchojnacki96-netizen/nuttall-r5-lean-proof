import W5.ThetaBulk48GeneratedVerifier

/-!
# First residual cell: executable finite-certificate diagnostic

This is a numerical diagnostic, not a theorem. It asks whether the already
real-sound signed interval generator has sufficiently sharp bounds for
the FIRST of the 48 remaining x-cells. It is deliberately not imported by
W5.lean, because proving R5 requires a true result for ALL cells.
-/

namespace W5

-- If this is false, refining numerical enclosures is required before
-- attempting a global native_decide theorem.
#eval thetaBulk48GeneratedCheck (821 / 2048 : ℚ) ((endpoints.drop 3).take 1)

-- Separately identify whether failure is already caused by Gaussian
-- range eligibility rather than by the exact rational LDL test.
#eval decide (ThetaBulkGaussianEligibility
  (821 / 2048 : ℚ) ((endpoints.drop 3).head!))

end W5
