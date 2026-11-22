import W5.ThetaOneSquareCellGammaBridge
import W5.ThetaAuditedMomentGammaCellBox

/-!
# Sound n=1 theta-term enclosures using the improved two-sided moments

Reuse the existing exact rational coefficient polynomial interval,
the original scale interval and the already proved signed nine-moment
interval evaluator. Only the moment boxes are replaced by the sharp
two-sided Gamma enclosure. No duplicate integration, Taylor remainder
proof, or interval arithmetic implementation.
-/

namespace W5

/-- An explicit computable-rational n=1 term interval on [a,b],
using the strong two-sided Gamma moment boxes for all nine moments. -/
noncomputable def thetaOneSquareCellTermQuadraticBox
    (a b : ℚ) (i j : Fin 5) : QInterval :=
  thetaAuditedOneTermMomentInterval
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaOneSquareCellCoefficientBox a b i j)
    (thetaNthQuadraticGammaMomentBox a b 1) 9

/-- Real-semantic soundness for the genuine original n=1 theta
summand on ANY nonnegative rational interval [a,b] with b≤1. -/
theorem thetaOneSquareCellTermQuadraticBox_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ))
    (hx : 0 < x) (hax : (a:ℝ) ≤ x)
    (hxb : x ≤ (b:ℝ)) (hb1 : (b:ℝ) ≤ 1)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaOneSquareCellTermQuadraticBox a b i j)
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
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx (hxb.trans hb1) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaOneSquareCellCoefficientBox a b i j)
    (thetaNthQuadraticGammaMomentBox a b 1)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaOneSquareCellCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ => by
      simpa only [Nat.cast_one, div_one] using
        (thetaNthQuadraticGammaMomentBox_containsReal
          a b x ha hax hxb hb1 1 k (by omega)))

end W5
