import Nuttall.PhiRankEightPolynomialPilot

namespace Nuttall

open scoped BigOperators

noncomputable def phiRankEightPolynomialRows (X q : ℝ) (i j : ℕ) : ℝ :=
  ∑ a ∈ Finset.range 8, ∑ b ∈ Finset.range 8,
    phiRankEightRow X i a * phiRankEightRow X j b *
      (q * (phiJetPolynomial (a+b)).eval (q*X))

macro "replay_rank_eight_polynomial" : tactic =>
  `(tactic| (
    unfold phiRankEightPolynomialRows
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd]
    simp (disch := decide) only [phiRankEightJet_eq_eval]
    norm_num [phiRankEightRow, phiRankEightJet, phiRankEightJetCoefficients,
      compactFixedRealEval, phiCompactPolynomial, phiCompactGaussian, Finset.sum_range_succ,
      Nat.factorial]
    ring <;> simp))

end Nuttall
