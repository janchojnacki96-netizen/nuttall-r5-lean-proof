import Nuttall.PhiRankEightPolynomialBand0
import Nuttall.PhiRankEightPolynomialBand1
import Nuttall.PhiRankEightPolynomialBand2
import Nuttall.PhiRankEightPolynomialBand3

namespace Nuttall

open scoped BigOperators

/-- Compare each polynomial entry with the two rows of the change of variables
applied to the theta derivative polynomials. -/
theorem phiRankEightPolynomial_eq_rows (X q : ℝ) (i j : ℕ) (hi : i < 8) (hj : j < 8) :
    phiCompactPolynomial X q i j =
      ∑ a ∈ Finset.range 8, ∑ b ∈ Finset.range 8,
        phiRankEightRow X i a * phiRankEightRow X j b *
          (q * (phiJetPolynomial (a+b)).eval (q*X)) := by
  change _ = phiRankEightPolynomialRows X q i j
  interval_cases i
  · exact phiRankEightPolynomial_band0 X q 0 j (Or.inl rfl) hj
  · exact phiRankEightPolynomial_band1 X q 1 j (Or.inl rfl) hj
  · exact phiRankEightPolynomial_band2 X q 2 j (Or.inl rfl) hj
  · exact phiRankEightPolynomial_band3 X q 3 j (Or.inl rfl) hj
  · exact phiRankEightPolynomial_band3 X q 4 j (Or.inr rfl) hj
  · exact phiRankEightPolynomial_band2 X q 5 j (Or.inr rfl) hj
  · exact phiRankEightPolynomial_band1 X q 6 j (Or.inr rfl) hj
  · exact phiRankEightPolynomial_band0 X q 7 j (Or.inr rfl) hj

#print axioms phiRankEightPolynomial_eq_rows

end Nuttall
