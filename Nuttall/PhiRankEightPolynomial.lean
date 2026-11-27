import Nuttall.PhiRankEightPolynomialPilot

namespace Nuttall

open scoped BigOperators

set_option maxHeartbeats 65000000 in
set_option maxRecDepth 32768 in
/-- Compare each polynomial entry with the two rows of the change of variables
applied to the theta derivative polynomials. -/
theorem phiRankEightPolynomial_eq_rows (X q : ℝ) (i j : ℕ) (hi : i < 8) (hj : j < 8) :
    phiCompactPolynomial X q i j =
      ∑ a ∈ Finset.range 8, ∑ b ∈ Finset.range 8,
        phiRankEightRow X i a * phiRankEightRow X j b *
          (q * (phiJetPolynomial (a+b)).eval (q*X)) := by
  interval_cases i <;> interval_cases j
  all_goals
    first
    | exact phiRankEightPolynomial_seven_seven X q
    | simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd]
      simp (disch := decide) only [phiRankEightJet_eq_eval]
      norm_num [phiRankEightRow, phiRankEightJet, phiRankEightJetCoefficients,
        compactFixedRealEval, phiCompactPolynomial, phiCompactGaussian, Finset.sum_range_succ,
        Nat.factorial]
      ring

#print axioms phiRankEightPolynomial_eq_rows

end Nuttall
