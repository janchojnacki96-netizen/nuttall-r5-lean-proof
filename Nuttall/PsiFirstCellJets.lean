import Nuttall.PsiCompactQuadrature
import Nuttall.PhiCompactExponential

namespace Nuttall

open W5
open scoped BigOperators

private def firstCenterExpBox : QInterval :=
  ⟨1.003913889338347573, 1.003913889338347574⟩

private def firstCenterCoordinateBox : QInterval :=
  ⟨3.191065539196598088, 3.191065539196598089⟩

private theorem firstCenterExpBox_containsReal :
    firstCenterExpBox.ContainsReal (Real.exp (1/256)) := by
  have hlo := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1/256 by norm_num) 20
  have hhi := Real.exp_bound' (n := 20) (show (0:ℝ) ≤ 1/256 by norm_num)
    (show (1:ℝ)/256 ≤ 1 by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  constructor <;> norm_num [firstCenterExpBox]
  · linarith only [hlo]
  · linarith only [hhi]

private theorem firstCenterCoordinateBox_containsReal :
    firstCenterCoordinateBox.ContainsReal (Real.pi * Real.exp (4*((1:ℝ)/256))) := by
  have hlo := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1/64 by norm_num) 20
  have hhi := Real.exp_bound' (n := 20) (show (0:ℝ) ≤ 1/64 by norm_num)
    (show (1:ℝ)/64 ≤ 1 by norm_num) (by decide)
  norm_num [Finset.sum_range_succ, Nat.factorial] at hlo hhi
  have hl : (1.015747708586685747458:ℝ) ≤ Real.exp (1/64) := by linarith only [hlo]
  have hu : Real.exp (1/64) ≤ (1.015747708586685747459:ℝ) := by linarith only [hhi]
  have hL := mul_le_mul Real.pi_gt_d20.le hl (by norm_num) Real.pi_pos.le
  have hU := mul_le_mul Real.pi_lt_d20.le hu (Real.exp_pos _).le (by norm_num)
  constructor <;> norm_num [firstCenterCoordinateBox]
  · norm_num at hL
    linarith only [hL]
  · norm_num at hU
    linarith only [hU]

private def firstCenterGaussianBox : QInterval :=
  phiCompactExpBox firstCenterCoordinateBox.lo firstCenterCoordinateBox.hi

private theorem firstCenterGaussianBox_containsReal :
    firstCenterGaussianBox.ContainsReal (Real.exp (-(Real.pi * Real.exp (4*((1:ℝ)/256))))) :=
  phiCompactExpBox_containsReal (by norm_num [firstCenterCoordinateBox])
    (by norm_num [firstCenterCoordinateBox]) firstCenterCoordinateBox_containsReal.1
    firstCenterCoordinateBox_containsReal.2

/-- Coefficients for the positive-order Ψ₁ derivatives at the first center.
Eight indices including the zero term suffice for this evaluator. -/
def psiOneFirstCellJetBox (j : ℕ) : QInterval :=
  QInterval.neg (phiCompactJetBox firstCenterExpBox firstCenterCoordinateBox
    firstCenterGaussianBox j 8)

set_option maxRecDepth 16384 in
theorem psiOneFirstCellJetBox_containsReal (j : ℕ) :
    (psiOneFirstCellJetBox j).ContainsReal (iteratedDeriv (j+1) (psi 1) (1/256)) := by
  rw [show (1:ℕ) = 0+1 by rfl, iteratedDeriv_succ_psi_succ]
  apply QInterval.neg_containsReal
  exact phiCompactJetBox_containsReal (by norm_num) (by norm_num)
    firstCenterExpBox_containsReal firstCenterCoordinateBox_containsReal
    firstCenterGaussianBox_containsReal (by norm_num [firstCenterCoordinateBox])
    (by decide +kernel) j 8 (by decide)

/-- The first cell's normalized Hankel coefficients, parameterized by an
interval for the one zeroth derivative that needs quadrature. -/
def psiOneFirstCellCoeffBox (corner : QInterval) (l k : ℕ) : QInterval :=
  let J := match l+k with
    | 0 => corner
    | j+1 => psiOneFirstCellJetBox j
  QInterval.mul (QInterval.point ((1/16:ℚ)^l * (1/256:ℚ)^k / (k.factorial:ℚ))) J

theorem psiOneFirstCellCoeffBox_containsReal {corner : QInterval}
    (hcorner : corner.ContainsReal (psi 1 (1/256))) (l k : ℕ) :
    (psiOneFirstCellCoeffBox corner l k).ContainsReal
      ((1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) (1/256)) := by
  have hs : (QInterval.point ((1/16:ℚ)^l * (1/256:ℚ)^k / (k.factorial:ℚ))).
      ContainsReal ((1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ)) := by
    simp only [QInterval.ContainsReal, QInterval.point, Rat.cast_pow, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat, le_refl, and_self]
  unfold psiOneFirstCellCoeffBox
  apply QInterval.mul_containsReal hs
  cases h : l+k with
  | zero => simpa only [iteratedDeriv_zero] using hcorner
  | succ j => exact psiOneFirstCellJetBox_containsReal j

/-- The actual first-cell Hankel entry has the enclosed polynomial
coefficients and the explicit remainder 10⁻¹⁹. The corner interval is
the only external datum needed on the analytic side. -/
theorem psiOne_compact_cell_contains_hankel {corner : QInterval}
    (hcorner : corner.ContainsReal (psi 1 (1/256)))
    (l : ℕ) (hl : l ≤ 12) {v : ℝ} (hv : |v| ≤ 1) :
    (∀ k ∈ Finset.range 25, (psiOneFirstCellCoeffBox corner l k).ContainsReal
      ((1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) (1/256))) ∧
    |(1/16:ℝ)^l * iteratedDeriv l (psi 1) (1/256 + (1/256)*v) -
      ∑ k ∈ Finset.range 25, ((1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) (1/256)) * v^k| ≤ (1:ℝ)/10^19 := by
  refine ⟨fun k _ => psiOneFirstCellCoeffBox_containsReal hcorner l k, ?_⟩
  have he :
      (1/16:ℝ)^l * cellTaylor (iteratedDeriv l (psi 1)) 24 (1/256) (1/256) v =
        ∑ k ∈ Finset.range 25, ((1/16:ℝ)^l * (1/256:ℝ)^k / (k.factorial:ℝ) *
          iteratedDeriv (l+k) (psi 1) (1/256)) * v^k := by
    rw [cellTaylor, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDeriv_iteratedDeriv_eq, Nat.add_comm k l]
    ring
  simpa only [mul_sub, he] using psiOne_first_cell_scaled_error_le l hl hv

#print axioms psiOne_compact_cell_contains_hankel

end Nuttall
