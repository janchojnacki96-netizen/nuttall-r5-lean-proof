import Nuttall.PhiOriginCertificate
import Nuttall.PhiJetCoefficientRows

namespace Nuttall

open W5
open scoped BigOperators

private def squareCoordinateBox (X : QInterval) (n : ℕ) : QInterval :=
  QInterval.mul (QInterval.point ((n:ℚ)^2)) X

private def phiJetTermBox (X q : QInterval) (j n : ℕ) : QInterval :=
  let Y := squareCoordinateBox X n
  let row := phiJetCoeffRow j
  let P := QInterval.sumBox (Finset.range (j+2)) (fun k =>
    QInterval.mul (QInterval.point row[k]!) (positivePowBox Y k))
  QInterval.mul (QInterval.mul Y P) (positivePowBox q (n^2))

/-- Shared interval evaluator for the first N terms of any real theta derivative.
Its three input boxes are for the exponential prefactor, the base coordinate
and its Gaussian, so the same base calculations serve every jet. -/
def phiJetPrefixBox (E X q : QInterval) (j N : ℕ) : QInterval :=
  QInterval.mul E (QInterval.sumBox (Finset.range N) (phiJetTermBox X q j))

private theorem auxiliaryWeightedSummand_eq_exp_powers (j n : ℕ) (t : ℝ) :
    auxiliaryWeightedSummand (phiJetPolynomial j) n t =
      Real.exp t *
        (auxiliaryCoordinate n t * (phiJetPolynomial j).eval (auxiliaryCoordinate n t) *
          Real.exp (-(Real.pi * Real.exp (4*t)))^(n^2)) := by
  rw [← Real.exp_nat_mul, Nat.cast_pow]
  unfold auxiliaryWeightedSummand auxiliarySummand auxiliaryCoordinate
  rw [show (5:ℝ)*t = t + 4*t by ring, Real.exp_add]
  rw [show (n:ℝ)^2 * -(Real.pi * Real.exp (4*t)) =
    -(n:ℝ)^2 * Real.pi * Real.exp (4*t) by ring]
  ring

/-- Soundness of the shared interval evaluator for a finite jet sum. -/
theorem phiJetPrefixBox_containsReal {E X q : QInterval} {t : ℝ}
    (hE : E.ContainsReal (Real.exp t)) (hX : X.ContainsReal (Real.pi * Real.exp (4*t)))
    (hq : q.ContainsReal (Real.exp (-(Real.pi * Real.exp (4*t)))))
    (hX₀ : 0 ≤ X.lo) (hq₀ : 0 ≤ q.lo) (j N : ℕ) :
    (phiJetPrefixBox E X q j N).ContainsReal
      (∑ n ∈ Finset.range N, auxiliaryWeightedSummand (phiJetPolynomial j) n t) := by
  simp_rw [auxiliaryWeightedSummand_eq_exp_powers]
  rw [← Finset.mul_sum]
  apply QInterval.mul_containsReal hE
  apply QInterval.sumBox_containsReal
  intro n _
  have hn : (QInterval.point ((n:ℚ)^2)).ContainsReal ((n:ℝ)^2) := by
    simp [QInterval.point, QInterval.ContainsReal]
  have hY : (squareCoordinateBox X n).ContainsReal (auxiliaryCoordinate n t) := by
    simpa only [squareCoordinateBox, auxiliaryCoordinate, mul_assoc] using
      QInterval.mul_containsReal hn hX
  have hY₀ : 0 ≤ (squareCoordinateBox X n).lo := by
    have hX₁ : 0 ≤ X.hi := hX₀.trans (by exact_mod_cast hX.1.trans hX.2)
    simp only [squareCoordinateBox, QInterval.mul, QInterval.point, le_min_iff]
    exact ⟨⟨mul_nonneg (sq_nonneg _) hX₀, mul_nonneg (sq_nonneg _) hX₁⟩,
      ⟨mul_nonneg (sq_nonneg _) hX₀, mul_nonneg (sq_nonneg _) hX₁⟩⟩
  apply QInterval.mul_containsReal _ (positivePowBox_containsReal hq₀ hq _)
  apply QInterval.mul_containsReal hY
  rw [eval_phiJetPolynomial_of_lt (by omega : j+1 < j+2)]
  apply QInterval.sumBox_containsReal
  intro k hk
  have h := Finset.mem_range.mp hk
  rw [getElem!_pos _ _ h, phiJetCoeffRow_getElem j k h]
  exact QInterval.mul_containsReal ⟨le_rfl, le_rfl⟩
    (positivePowBox_containsReal hY₀ hY k)

#print axioms phiJetPrefixBox_containsReal

end Nuttall
