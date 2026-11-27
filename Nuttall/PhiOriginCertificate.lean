import Nuttall.OriginWronskianInterval
import Nuttall.OriginGaussianBounds
import Nuttall.PhiOriginTail

namespace Nuttall

open W5
open scoped BigOperators

private def originCoordinateBox (n : ℕ) : QInterval :=
  ⟨(n:ℚ)^2 * 3.14159265358979323846, (n:ℚ)^2 * 3.14159265358979323847⟩

private def originGaussianBaseBox : QInterval :=
  ⟨0.0432139182637, 0.0432139182639⟩

/-- Raising a nonnegative interval to a natural power only uses its endpoints. -/
def positivePowBox (B : QInterval) (k : ℕ) : QInterval :=
  ⟨B.lo^k, B.hi^k⟩

theorem positivePowBox_containsReal {B : QInterval} {x : ℝ}
    (h₀ : 0 ≤ B.lo) (h : B.ContainsReal x) (k : ℕ) :
    (positivePowBox B k).ContainsReal (x^k) := by
  have hb : (0:ℝ) ≤ (B.lo:ℝ) := by exact_mod_cast h₀
  simpa only [QInterval.ContainsReal, positivePowBox, Rat.cast_pow] using
    And.intro (pow_le_pow_left₀ hb h.1 k) (pow_le_pow_left₀ (hb.trans h.1) h.2 k)

private def phiOriginPolynomialBox (j n : ℕ) : QInterval :=
  QInterval.sumBox (Finset.range 10) (fun k =>
    QInterval.mul (QInterval.point (phiJetCoeff j k)) (positivePowBox (originCoordinateBox n) k))

private def phiOriginTermBox (j n : ℕ) : QInterval :=
  QInterval.mul (QInterval.mul (originCoordinateBox n) (phiOriginPolynomialBox j n))
    (positivePowBox originGaussianBaseBox (n^2))

private theorem phiOriginTermBox_containsReal {j : ℕ} (hj : j ≤ 8) (n : ℕ) :
    (phiOriginTermBox j n).ContainsReal (auxiliaryWeightedSummand (phiJetPolynomial j) n 0) := by
  let x := (n:ℝ)^2 * Real.pi
  have hlo : ((3.14159265358979323846 : ℚ) : ℝ) = 3.14159265358979323846 := by norm_num
  have hhi : ((3.14159265358979323847 : ℚ) : ℝ) = 3.14159265358979323847 := by norm_num
  have hx : (originCoordinateBox n).ContainsReal x := by
    simpa only [QInterval.ContainsReal, originCoordinateBox, x, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, hlo, hhi] using
      And.intro (mul_le_mul_of_nonneg_left Real.pi_gt_d20.le (sq_nonneg (n:ℝ)))
        (mul_le_mul_of_nonneg_left Real.pi_lt_d20.le (sq_nonneg (n:ℝ)))
  have hx₀ : 0 ≤ (originCoordinateBox n).lo := by dsimp [originCoordinateBox]; positivity
  have hqlo : ((0.0432139182637 : ℚ) : ℝ) = 0.0432139182637 := by norm_num
  have hqhi : ((0.0432139182639 : ℚ) : ℝ) = 0.0432139182639 := by norm_num
  have hq : originGaussianBaseBox.ContainsReal (Real.exp (-Real.pi)) := by
    simpa only [QInterval.ContainsReal, originGaussianBaseBox, hqlo, hqhi] using exp_neg_pi_bounds
  have hp : (phiOriginPolynomialBox j n).ContainsReal ((phiJetPolynomial j).eval x) := by
    rw [eval_phiJetPolynomial hj]
    apply QInterval.sumBox_containsReal
    intro k _
    apply QInterval.mul_containsReal
    · exact ⟨le_rfl, le_rfl⟩
    · exact positivePowBox_containsReal hx₀ hx k
  rw [auxiliaryWeightedSummand_origin]
  exact QInterval.mul_containsReal (QInterval.mul_containsReal hx hp)
    (positivePowBox_containsReal (by norm_num [originGaussianBaseBox]) hq _)

private def phiOriginSeriesBox (j : ℕ) : QInterval :=
  QInterval.add (QInterval.sumBox (Finset.range 8) (phiOriginTermBox j))
    ⟨-(1/10^12), 1/10^12⟩

private theorem phiOriginSeriesBox_containsReal {j : ℕ} (hj : j ≤ 8) :
    (phiOriginSeriesBox j).ContainsReal (iteratedDeriv j Phi 0) := by
  rw [iteratedDeriv_phi_eq_tsum,
    ← (auxiliaryWeightedSummand_summable (phiJetPolynomial j) 0).sum_add_tsum_nat_add 8]
  apply QInterval.add_containsReal
  · exact QInterval.sumBox_containsReal _ _ _ (fun n _ => phiOriginTermBox_containsReal hj n)
  · have hb := abs_le.mp (phiOriginTail_abs_le hj)
    simpa only [QInterval.ContainsReal, Rat.cast_div, Rat.cast_neg, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat] using hb

set_option maxRecDepth 16384 in
set_option maxHeartbeats 6000000 in
private theorem phiOriginSeriesBox_subset {j : ℕ} (hj : j ≤ 8) :
    (phiOriginJetBox j).lo ≤ (phiOriginSeriesBox j).lo ∧
      (phiOriginSeriesBox j).hi ≤ (phiOriginJetBox j).hi := by
  interval_cases j <;> decide +kernel

/-- Exact-rational enclosures of the nine real derivatives used by the origin witness. -/
theorem phiOriginJet_bounds (j : ℕ) (hj : j ≤ 8) :
    (phiOriginJetBox j).ContainsReal (iteratedDeriv j Phi 0) := by
  have hs := phiOriginSeriesBox_subset hj
  have ht := phiOriginSeriesBox_containsReal hj
  have hl : ((phiOriginJetBox j).lo : ℝ) ≤ ((phiOriginSeriesBox j).lo : ℝ) := by exact_mod_cast hs.1
  have hh : ((phiOriginSeriesBox j).hi : ℝ) ≤ ((phiOriginJetBox j).hi : ℝ) := by exact_mod_cast hs.2
  exact ⟨hl.trans ht.1, ht.2.trans hh⟩

/-- The strict rank-five obstruction at integration level zero. -/
theorem phi_origin_wronskian_neg : wronskian Phi 5 0 < 0 :=
  phi_origin_wronskian_neg_of_jet_bounds phiOriginJet_bounds

#print axioms phiOriginJet_bounds
#print axioms phi_origin_wronskian_neg

end Nuttall
