import W5.ThetaAuditedMomentGammaBox
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

/-- Gamma enclosure for the true n=1 weighted moment, for any
rational upper endpoint b. This extends the already-proved b=1/8
estimate without requiring endpoint quadrature. -/
def thetaOneSquareGammaMomentBox (b : ℚ) (k : ℕ) : QInterval :=
  ⟨(Nat.factorial k : ℚ),
    (Nat.factorial k : ℚ) +
      b^2 * (Nat.factorial (k+1) : ℚ)⟩

theorem thetaOneSquareGammaMomentBox_containsReal
    (b : ℚ) (hb1 : (b : ℝ) ≤ 1)
    (x : ℝ) (hx0 : 0 ≤ x) (hxb : x ≤ (b : ℝ))
    (k : ℕ) :
    QInterval.ContainsReal (thetaOneSquareGammaMomentBox b k)
      (thetaAuditedOneWeightedMoment x k) := by
  have hx1 : x ≤ 1 := hxb.trans hb1
  have hb0 : (0 : ℝ) ≤ (b : ℝ) := hx0.trans hxb
  have hsq : x^2 ≤ (b : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hxb) (add_nonneg hx0 hb0)]
  have hlo := thetaAuditedOneWeightedMoment_gamma_lower x hx0 hx1 k
  have hu := thetaAuditedOneWeightedMoment_gamma_upper x hx0 hx1 k
  have hfac : (0 : ℝ) ≤ (Nat.factorial (k+1) : ℝ) := by positivity
  have hupper :
      thetaAuditedOneWeightedMoment x k ≤
        (Nat.factorial k : ℝ) +
          (b : ℝ)^2 * (Nat.factorial (k+1) : ℝ) := by
    calc
      _ ≤ (Nat.factorial k : ℝ) +
          x^2 * (Nat.factorial (k+1) : ℝ) := hu
      _ ≤ (Nat.factorial k : ℝ) +
          (b : ℝ)^2 * (Nat.factorial (k+1) : ℝ) := by
            gcongr
  simpa only [QInterval.ContainsReal, thetaOneSquareGammaMomentBox,
    Rat.cast_natCast, Rat.cast_add, Rat.cast_mul, Rat.cast_pow] using
    (show (Nat.factorial k : ℝ) ≤ thetaAuditedOneWeightedMoment x k ∧
      thetaAuditedOneWeightedMoment x k ≤
        (Nat.factorial k : ℝ) +
          (b : ℝ)^2 * (Nat.factorial (k+1) : ℝ) from
      ⟨hlo, hupper⟩)

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
    (thetaOneSquareGammaMomentBox b) 9

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
    (thetaOneSquareGammaMomentBox b)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaOneSquareCellCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ =>
      thetaOneSquareGammaMomentBox_containsReal
        b hb1 x hx.le hxb k)

end W5
