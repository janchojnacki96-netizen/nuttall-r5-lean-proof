import W5.ThetaCoarseGammaMomentBoxes
import W5.ThetaFirstCellRationalCoefficientCertificate
import W5.ThetaFirstCellGammaUniformCandidate

/-!
# Reusable genuine n=1 theta-term enclosure on an arbitrary rational x-cell

The already verified first-cell proof uses the nine genuine Lebesgue
weighted moments and a rational bivariate polynomial for the n=1 term.
Those ingredients do not intrinsically require b=1/8.

This module reuses:
* the original Mathlib Gamma upper/lower estimates, without reintegrating;
* the existing exact rational-to-real polynomial interval evaluator;
* the existing nine-moment interval soundness theorem and signed arithmetic.

For 0 < x in [a,b] with b <= 1, it constructs a *real-sound*
rational interval for the original n=1 square-index summand.
No claim is made about n=2,...,11, about containment in the much
tighter imported 768-bit cell matrices, or about complete R5.
-/

namespace W5

/-!
The general refined Gamma enclosure for all n>0 already exists in
ThetaCoarseGammaMomentBoxes on the earlier working branch.
Its original Git blob is imported unchanged here. Specialize the improved quarter-Gamma estimate to n=1
instead of proving the same inequality a second time.
-/

/-- The same exact rational polynomial from the original first-cell
certificate, evaluated on an arbitrary rational cell. -/
noncomputable def thetaOneSquareCellCoefficientBox
    (a b : ℚ) (i j : Fin 5) (k : ℕ) : QInterval :=
  thetaRationalPolynomialInterval
    (thetaFirstCellCoefficientRationalPolynomial i j k)
    ⟨a, b⟩

theorem thetaOneSquareCellCoefficientBox_containsReal
    (a b : ℚ) (x : ℝ)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (i j : Fin 5) (k : ℕ) :
    QInterval.ContainsReal
      (thetaOneSquareCellCoefficientBox a b i j k)
      ((thetaCorrectionWPolynomial x 1 0 i j).coeff k) := by
  have hcell : QInterval.ContainsReal (⟨a, b⟩ : QInterval) x :=
    ⟨hax, hxb⟩
  have h := thetaRationalPolynomialInterval_containsReal
    (thetaFirstCellCoefficientRationalPolynomial i j k)
    (⟨a, b⟩ : QInterval) x hcell
  change QInterval.ContainsReal
    (thetaOneSquareCellCoefficientBox a b i j k)
    ((thetaFirstCellCoefficientRationalPolynomial i j k).eval₂
      (Rat.castHom ℝ) x) at h
  rw [thetaFirstCellCoefficientRationalPolynomial_eval] at h
  exact h

/-- A fully rational scale enclosure. It uses the already-proved
four-corner interval multiplication rather than a new square routine. -/
def thetaOneSquareCellScaleBox (a b : ℚ) : QInterval :=
  QInterval.mul
    (QInterval.mul ⟨a, b⟩ ⟨a, b⟩)
    ⟨1/4, 1/4⟩

theorem thetaOneSquareCellScaleBox_containsReal
    (a b : ℚ) (x : ℝ)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    QInterval.ContainsReal
      (thetaOneSquareCellScaleBox a b) (x^2/4) := by
  have hcell : QInterval.ContainsReal (⟨a, b⟩ : QInterval) x :=
    ⟨hax, hxb⟩
  have hquarter :
      QInterval.ContainsReal (⟨1/4, 1/4⟩ : QInterval) (1/4 : ℝ) := by
    norm_num [QInterval.ContainsReal]
  have hmul :
      QInterval.ContainsReal
        (thetaOneSquareCellScaleBox a b) (x*x*(1/4 : ℝ)) := by
    exact QInterval.mul_containsReal
      (QInterval.mul_containsReal hcell hcell) hquarter
  convert hmul using 1 <;> ring

/-- Uniform interval for the actual n=1 theta summand on [a,b].
The diagonal, nine original polynomial coefficients, moment bounds,
and scale all come from existing formally proved constructions. -/
noncomputable def thetaOneSquareCellTermBox
    (a b : ℚ) (i j : Fin 5) : QInterval :=
  thetaAuditedOneTermMomentInterval
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaOneSquareCellCoefficientBox a b i j)
    (thetaNthQuarterGammaMomentBox b 1) 9

theorem thetaOneSquareCellTermBox_containsReal
    (a b : ℚ) (x : ℝ)
    (hx : 0 < x) (hax : (a : ℝ) ≤ x)
    (hxb : x ≤ (b : ℝ)) (hb1 : (b : ℝ) ≤ 1)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaOneSquareCellTermBox a b i j)
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
    (thetaNthQuarterGammaMomentBox b 1)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaOneSquareCellCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ => by
      simpa only [Nat.cast_one, div_one] using
        (thetaNthQuarterGammaMomentBox_containsReal
          b x hx.le hxb hb1 1 k (by omega)))

end W5
