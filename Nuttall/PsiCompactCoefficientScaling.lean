import Nuttall.CompactIntervalRounding
import W5.VerifiedIntervalPolynomials

namespace Nuttall

open W5

/-- Scale the Hankel indices and the Taylor variable before rounding outward. -/
def psiOneCompactCoefficientBoxOfJet (radius : ℚ) (J : QInterval) (l k : ℕ) : QInterval :=
  compactRoundInterval (2^90) (QInterval.mul
    (QInterval.point ((1/16:ℚ)^l * radius^k / (k.factorial:ℚ)))
    J)

theorem psiOneCompactCoefficientBoxOfJet_containsReal {radius : ℚ} {J : QInterval} {x : ℝ}
    (hJ : J.ContainsReal x) (l k : ℕ) :
    (psiOneCompactCoefficientBoxOfJet radius J l k).ContainsReal
      ((1/16:ℝ)^l * (radius:ℝ)^k / (k.factorial:ℝ) * x) := by
  have hs : QInterval.ContainsReal
      (QInterval.point ((1/16:ℚ)^l * radius^k / (k.factorial:ℚ)))
      ((1/16:ℝ)^l * (radius:ℝ)^k / (k.factorial:ℝ)) := by
    simp only [QInterval.ContainsReal, QInterval.point, Rat.cast_pow, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, le_refl, and_self]
  unfold psiOneCompactCoefficientBoxOfJet
  apply compactRoundInterval_containsReal (by positivity)
  exact QInterval.mul_containsReal hs hJ

end Nuttall
