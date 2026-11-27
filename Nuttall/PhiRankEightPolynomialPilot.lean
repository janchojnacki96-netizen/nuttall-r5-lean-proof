import Nuttall.PhiCompactNormalization
import Nuttall.PhiRankEightChangeOfVariables

namespace Nuttall

open scoped BigOperators

set_option maxHeartbeats 25000000 in
set_option maxRecDepth 32768 in
/-- The largest pair of indices in the rank-eight polynomial comparison. -/
theorem phiRankEightPolynomial_seven_seven (X q : ℝ) :
    phiCompactPolynomial X q 7 7 =
      ∑ a ∈ Finset.range 8, ∑ b ∈ Finset.range 8,
        phiRankEightRow X 7 a * phiRankEightRow X 7 b *
          (q * (phiJetPolynomial (a+b)).eval (q*X)) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd]
  simp (disch := decide) only [phiRankEightJet_eq_eval]
  norm_num [phiRankEightRow, phiRankEightJet, phiRankEightJetCoefficients,
    compactFixedRealEval, phiCompactPolynomial, phiCompactGaussian, Finset.sum_range_succ,
    Nat.factorial]
  ring

#print axioms phiRankEightPolynomial_seven_seven

end Nuttall
