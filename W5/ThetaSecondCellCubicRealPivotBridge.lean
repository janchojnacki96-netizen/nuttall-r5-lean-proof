import W5.ThetaSecondCellCubicFirstSquareReal
import W5.ThetaSecondCellCubicWidenedLDL
import W5.ThetaSymmetric15EntryCellCertificates
import W5.ThetaAuditedTailRationalEnclosure

/-!
# Reduce all five REAL theta pivot signs on cell 2 to ONE tail bound

Reuse:
* the genuine n=1 interval soundness theorem for ALL entries,
* the existing unconditional thetaCoefficient prefix/tail identity,
* real-sound rational QInterval addition,
* the existing symmetric 15-entry completion and real interval LDL,
* the one finite rational 5-pivot check of the widened matrix.

The ONLY remaining analytic premise for this cell is a single
uniform bound on the genuine n>=2 infinite tail, for all 15
independent entries (equivalently 25 entries by symmetry).
No determinant or numerical calculation is repeated here.
-/

namespace W5

/-- The true original coefficient is enclosed by the wider
cubic-Gamma interval whenever its true remaining n>=2 tail
has absolute value at most 1/100. -/
theorem thetaSecondCellCubicWidenedMatrix_containsReal_of_tail
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (htail : ∀ i j : Fin 5,
      |thetaAuditedTail 2 x i j| ≤ (1:ℝ)/100)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaSecondCellCubicWidenedMatrix i j)
      (thetaCoefficient x i j) := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
  have hOne :=
    thetaSecondCellCubicFirstSquareMatrix_containsReal
      x hax hxb i j
  have hTail :
      QInterval.ContainsReal thetaSecondCellUniformTailAllowance
        (thetaAuditedTail 2 x i j) := by
    have h := abs_le.mp (htail i j)
    simpa [thetaSecondCellUniformTailAllowance,
      QInterval.ContainsReal] using h
  have hSplit :
      thetaCoefficient x i j =
        thetaAuditedSeriesTerm x i j 1 +
          thetaAuditedTail 2 x i j := by
    rw [thetaCoefficient_eq_audited_prefix_add_tail_unconditional
      2 x hx hx1 i j]
    rw [thetaAuditedPrefix_two_eq_one]
  rw [hSplit]
  exact QInterval.add_containsReal hOne hTail

/-- One common n>=2 tail bound implies all five alternating
REAL original theta pivot signs throughout the second cell.
This is conditional until that UNIFORM analytic bound is supplied. -/
theorem thetaSecondCellCubicRealPivotSigns_of_tail
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (htail : ∀ i j : Fin 5,
      |thetaAuditedTail 2 x i j| ≤ (1:ℝ)/100) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  have hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal
        ((thetaSymmetricIntervals thetaSecondCellCubicWidenedMatrix) i j)
        (thetaCoefficient x i j) := by
    intro i j
    exact thetaSymmetricIntervals_contains_theta
      thetaSecondCellCubicWidenedMatrix x
      (fun k l _ =>
        thetaSecondCellCubicWidenedMatrix_containsReal_of_tail
          x hax hxb htail k l) i j
  exact thetaFive_pivotSigns_of_interval x
    (thetaSymmetricIntervals thetaSecondCellCubicWidenedMatrix)
    hentry thetaSecondCellCubicWidenedMatrix_pivotSigns

end W5
