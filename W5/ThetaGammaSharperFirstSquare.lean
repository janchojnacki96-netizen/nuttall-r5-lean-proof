import W5.ThetaGammaAutoCellMomentBox
import W5.ThetaGenericCubicGammaCellCertificate

/-!
# Replace the old broad nine Gamma moments in the TRUE n=1 theta matrix

The original 48-cell evaluator reuses thetaNthCubicGammaMomentBox,
whose global third-order Taylor envelopes may be too broad for the
fifth LDL pivot. The FULL original moments can now be enclosed by
the independently sound rational Gamma-grid algorithm.

This module changes only the moment generator; it reuses exactly
the existing original n=1 polynomial coefficients, scale,
diagonal, nine-moment finite sum, and genuine real soundness lemma.
A single proof covers all 25 matrix entries.
-/

namespace W5

/-- Exact-rational n=1 theta matrix using 9 certified full moments
at the endpoints of the original x-cell, rather than global
quadratic/cubic Gamma moment bounds. -/
def thetaGammaSharperFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ) :
    ThetaIntervalMatrix :=
  fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      (fun k => thetaGammaAutoCellMomentBox steps k a b 1 us) 9

/-- Every entry of the generated n=1 matrix encloses its TRUE
original theta series summand. Only TWO rational endpoint grid
checks, independent of i,j,k, are needed. -/
theorem thetaGammaSharperFirstSquareMatrix_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaGammaSharperFirstSquareMatrix steps a b us i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  have hdiag : QInterval.ContainsReal
      (thetaFirstCellGammaUniformDiagonal i j)
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) := by
    by_cases hij : i = j
    · subst j
      simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, Rat.cast_div, Rat.cast_pow]
    · simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, hij]
  have hM (k : ℕ) :
      QInterval.ContainsReal
        (thetaGammaAutoCellMomentBox steps k a b 1 us)
        (thetaAuditedOneWeightedMoment x k) := by
    have hA1 : thetaGammaAutoMomentCheck
        steps (a/(1:ℚ)) us = true := by simpa using hA
    have hB1 : thetaGammaAutoMomentCheck
        steps (b/(1:ℚ)) us = true := by simpa using hB
    have hm := thetaGammaAutoCellMomentBox_containsReal
      steps k a b 1 us x ha (by norm_num) hax hxb hb1
      hA1 hB1
    simpa only [Nat.cast_one, div_one] using hm
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx (hxb.trans hb1) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
    (fun k => thetaGammaAutoCellMomentBox steps k a b 1 us)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaGeneralCellCubicBinomialCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ => hM k)

end W5
