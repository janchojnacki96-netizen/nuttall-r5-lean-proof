import Nuttall.PhiRankEightPolynomialReplay

namespace Nuttall

set_option maxHeartbeats 65000000 in
set_option maxRecDepth 32768 in
theorem phiRankEightPolynomial_band2 (X q : ℝ) (i j : ℕ) (hi : i = 2 ∨ i = 5)
    (hj : j < 8) : phiCompactPolynomial X q i j = phiRankEightPolynomialRows X q i j := by
  rcases hi with rfl | rfl <;> interval_cases j
  all_goals first | exact phiRankEightPolynomial_seven_seven X q | replay_rank_eight_polynomial

end Nuttall
