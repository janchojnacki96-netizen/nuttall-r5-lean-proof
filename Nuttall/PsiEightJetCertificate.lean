import Nuttall.PhiCompactExponential
import Nuttall.PhiOriginCertificate
import Nuttall.PsiEightJetTail
import Nuttall.PsiHankelJets

namespace Nuttall

open W5
open scoped BigOperators

private noncomputable def witnessTime : ℝ := 5/64
private noncomputable def witnessCoordinate : ℝ := Real.pi * Real.exp (4*witnessTime)

private def expTimeBox : QInterval :=
  ⟨1.08125780744903960314, 1.08125780744903960315⟩

private def coordinateBox : QInterval := ⟨4.294048034639396625, 4.294048034639396626⟩

private theorem expTimeBox_containsReal :
    expTimeBox.ContainsReal (Real.exp witnessTime) := by
  have hlo := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/64 by norm_num) 20
  have hhi := Real.exp_bound' (n := 20) (show (0:ℝ) ≤ 5/64 by norm_num)
    (show (5:ℝ)/64 ≤ 1 by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  constructor <;> norm_num [expTimeBox, witnessTime]
  · linarith only [hlo]
  · linarith only [hhi]

private theorem coordinateBox_containsReal : coordinateBox.ContainsReal witnessCoordinate := by
  have hlo := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 5/16 by norm_num) 20
  have hhi := Real.exp_bound' (n := 20) (show (0:ℝ) ≤ 5/16 by norm_num)
    (show (5:ℝ)/16 ≤ 1 by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  have hlo' : (1.36683794117379636283:ℝ) ≤ Real.exp (5/16) := by linarith only [hlo]
  have hhi' : Real.exp (5/16) ≤ (1.36683794117379636284:ℝ) := by linarith only [hhi]
  have hl := mul_le_mul Real.pi_gt_d20.le hlo' (by norm_num) Real.pi_pos.le
  have hu := mul_le_mul Real.pi_lt_d20.le hhi' (Real.exp_pos _).le (by norm_num)
  have he : (4:ℝ) * witnessTime = 5/16 := by norm_num [witnessTime]
  unfold witnessCoordinate
  rw [he]
  constructor <;> norm_num [coordinateBox]
  · norm_num at hl
    linarith only [hl]
  · norm_num at hu
    linarith only [hu]

private def gaussianBox : QInterval :=
  ⟨0.0136495594218404279438, 0.0136495594224116746484⟩

private theorem gaussianBox_containsReal : gaussianBox.ContainsReal (Real.exp (-witnessCoordinate)) := by
  have h := phiCompactExpBox_containsReal
    (by norm_num [coordinateBox] : 0 ≤ coordinateBox.lo)
    (by norm_num [coordinateBox] : coordinateBox.hi ≤ 16)
    coordinateBox_containsReal.1 coordinateBox_containsReal.2
  have hl : gaussianBox.lo ≤ (phiCompactExpBox coordinateBox.lo coordinateBox.hi).lo := by
    decide +kernel
  have hu : (phiCompactExpBox coordinateBox.lo coordinateBox.hi).hi ≤ gaussianBox.hi := by
    decide +kernel
  exact ⟨(Rat.cast_mono hl).trans h.1, h.2.trans (Rat.cast_mono hu)⟩

private def jetCoordinateBox (n : ℕ) : QInterval :=
  QInterval.mul (QInterval.point ((n:ℚ)^2)) coordinateBox

private theorem jetCoordinateBox_nonneg (n : ℕ) : 0 ≤ (jetCoordinateBox n).lo := by
  simp only [jetCoordinateBox, QInterval.mul, QInterval.point, le_min_iff]
  norm_num [coordinateBox]

private def jetPolynomialBox (j n : ℕ) : QInterval :=
  QInterval.sumBox (Finset.range (j+2)) (fun k =>
    QInterval.mul (QInterval.point (phiJetCoeff j k)) (positivePowBox (jetCoordinateBox n) k))

private def jetTermBox (j n : ℕ) : QInterval :=
  QInterval.mul (QInterval.mul (jetCoordinateBox n) (jetPolynomialBox j n))
    (positivePowBox gaussianBox (n^2))

private theorem jetTermBox_containsReal (j n : ℕ) :
    (jetTermBox j n).ContainsReal
      (auxiliaryCoordinate n witnessTime * (phiJetPolynomial j).eval (auxiliaryCoordinate n witnessTime) *
        Real.exp (-witnessCoordinate)^(n^2)) := by
  have hx : (jetCoordinateBox n).ContainsReal (auxiliaryCoordinate n witnessTime) := by
    have hs : (QInterval.point ((n:ℚ)^2)).ContainsReal ((n:ℝ)^2) := by
      simp [QInterval.ContainsReal, QInterval.point]
    simpa only [jetCoordinateBox, auxiliaryCoordinate, witnessCoordinate, mul_assoc] using
      QInterval.mul_containsReal hs coordinateBox_containsReal
  have hp : (jetPolynomialBox j n).ContainsReal
      ((phiJetPolynomial j).eval (auxiliaryCoordinate n witnessTime)) := by
    rw [eval_phiJetPolynomial_of_lt (by omega : j+1 < j+2)]
    apply QInterval.sumBox_containsReal
    intro k _
    exact QInterval.mul_containsReal ⟨le_rfl, le_rfl⟩
      (positivePowBox_containsReal (jetCoordinateBox_nonneg n) hx k)
  exact QInterval.mul_containsReal (QInterval.mul_containsReal hx hp)
    (positivePowBox_containsReal (by norm_num [gaussianBox]) gaussianBox_containsReal _)

private theorem weightedSummand_eq (j n : ℕ) :
    auxiliaryWeightedSummand (phiJetPolynomial j) n witnessTime =
      Real.exp witnessTime *
        (auxiliaryCoordinate n witnessTime * (phiJetPolynomial j).eval (auxiliaryCoordinate n witnessTime) *
          Real.exp (-witnessCoordinate)^(n^2)) := by
  rw [← Real.exp_nat_mul, Nat.cast_pow]
  unfold auxiliaryWeightedSummand auxiliarySummand auxiliaryCoordinate witnessCoordinate
  rw [show (5:ℝ)*witnessTime = witnessTime + 4*witnessTime by ring, Real.exp_add]
  rw [show (n:ℝ)^2 * -(Real.pi * Real.exp (4*witnessTime)) =
    -(n:ℝ)^2 * Real.pi * Real.exp (4*witnessTime) by ring]
  ring

/-- Exact rational intervals for the positive-order jets before outward rounding. -/
def psiEightJetRawBox (j : ℕ) : QInterval :=
  QInterval.neg (QInterval.add
    (QInterval.mul expTimeBox (QInterval.sumBox (Finset.range 9) (jetTermBox j)))
    ⟨-1/10^12, 1/10^12⟩)

/-- The interval encloses the actual derivative of the first tail integral. -/
theorem psiEightJetRawBox_containsReal {j : ℕ} (hj : j ≤ 13) :
    (psiEightJetRawBox j).ContainsReal (iteratedDeriv (j+1) (psi 1) (5/64)) := by
  change (psiEightJetRawBox j).ContainsReal (iteratedDeriv (j+1) (psi 1) witnessTime)
  rw [iteratedDeriv_succ_psi_one_eq_tsum,
    ← (auxiliaryWeightedSummand_summable (phiJetPolynomial j) witnessTime).sum_add_tsum_nat_add 9]
  apply QInterval.neg_containsReal
  apply QInterval.add_containsReal
  · simp_rw [weightedSummand_eq]
    rw [← Finset.mul_sum]
    exact QInterval.mul_containsReal expTimeBox_containsReal
      (QInterval.sumBox_containsReal _ _ _ (fun n _ => jetTermBox_containsReal j n))
  · have ht : witnessTime ≤ 1 := by norm_num [witnessTime]
    have hX : 4 ≤ witnessCoordinate := le_trans (by norm_num [coordinateBox]) coordinateBox_containsReal.1
    have h := abs_le.mp (rankEight_phiJetTail_abs_le hj ht hX)
    simpa only [QInterval.ContainsReal, Rat.cast_div, Rat.cast_neg, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat, neg_div] using h

#print axioms psiEightJetRawBox_containsReal

end Nuttall
