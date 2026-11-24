import W5.ThetaSecondCellCubicFirstSquareMatrix
import W5.ThetaFirstCellComputableCoefficientBound

/-!
# Real-semantic validity of the new computable second-cell n=1 matrix

The existing original coefficient identity
thetaFirstCell_original_coeff_binomial is used directly, rather
than reproducing the nested polynomial map and degree arguments.

Every binomial summand is enclosed by an exact rational interval
using Mathlib/previously verified QInterval power and multiplication.
The finite sum is sound by the EXISTING finsetSum_containsReal.
The nine genuine Gamma moments have the new proved cubic-upper
and old quadratic-lower boxes.

This covers only the true n=1 term. Uniform bounds for n>=2
are a separate analytic step before the original thetaCoefficient
or its LDL signs can be certified.
-/

namespace W5

/-- Each computable binomial coefficient interval contains the
corresponding ORIGINAL real w-polynomial coefficient, for every
x on the entire second rational cell and every i,j,k. -/
theorem thetaSecondCellCubicBinomialCoefficientBox_containsReal
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (i j : Fin 5) (k : ℕ) :
    QInterval.ContainsReal
      (thetaSecondCellCubicBinomialCoefficientBox i j k)
      ((thetaCorrectionWPolynomial x 1 0 i j).coeff k) := by
  have hxBox : QInterval.ContainsReal
      (⟨1/8, 177/512⟩ : QInterval) x := by
    change ((1/8:ℚ) : ℝ) ≤ x ∧
      x ≤ ((177/512:ℚ) : ℝ)
    norm_num
    exact ⟨hax, hxb⟩
  rw [thetaFirstCell_original_coeff_binomial]
  apply QInterval.finsetSum_containsReal
    (Finset.range (min i.val j.val + 1))
    (fun t =>
      let m : ℕ := i.val+j.val-2*t
      let u : ℕ := k-m
      if m ≤ k then
        QInterval.mul
          (QInterval.point
            (((-1:ℚ)^(i.val+j.val-t)) /
              ((Nat.factorial t : ℚ) *
               (Nat.factorial (i.val-t) : ℚ) *
               (Nat.factorial (j.val-t) : ℚ)) *
               (t.choose u : ℚ)))
          (QInterval.pow (⟨1/8,177/512⟩ : QInterval) (m+2*u))
      else QInterval.point 0)
    (fun t =>
      (((-1 : ℝ)^(i.val+j.val-t)) /
        ((Nat.factorial t : ℝ) *
         (Nat.factorial (i.val-t) : ℝ) *
         (Nat.factorial (j.val-t) : ℝ))) *
      (if i.val+j.val-2*t ≤ k then
        x^(i.val+j.val-2*t) *
          ((t.choose (k-(i.val+j.val-2*t)) : ℝ) *
            (x^2)^(k-(i.val+j.val-2*t)))
       else 0))
    (by
      intro t ht
      let m : ℕ := i.val+j.val-2*t
      let u : ℕ := k-m
      change QInterval.ContainsReal
        (if m ≤ k then
          QInterval.mul
            (QInterval.point
              (((-1:ℚ)^(i.val+j.val-t)) /
                ((Nat.factorial t : ℚ) *
                 (Nat.factorial (i.val-t) : ℚ) *
                 (Nat.factorial (j.val-t) : ℚ)) *
                 (t.choose u : ℚ)))
            (QInterval.pow (⟨1/8,177/512⟩ : QInterval) (m+2*u))
          else QInterval.point 0)
        (((( -1 : ℝ)^(i.val+j.val-t)) /
          ((Nat.factorial t : ℝ) *
           (Nat.factorial (i.val-t) : ℝ) *
           (Nat.factorial (j.val-t) : ℝ))) *
        (if m ≤ k then
          x^m * ((t.choose u : ℝ) * (x^2)^u)
         else 0))
      by_cases hmk : m ≤ k
      · simp only [if_pos hmk]
        have hc :=
          thetaRationalPoint_containsReal
            (((-1:ℚ)^(i.val+j.val-t)) /
              ((Nat.factorial t : ℚ) *
               (Nat.factorial (i.val-t) : ℚ) *
               (Nat.factorial (j.val-t) : ℚ)) *
               (t.choose u : ℚ))
        have hp :=
          thetaRationalIntervalPow_containsReal
            (⟨1/8,177/512⟩ : QInterval) x hxBox (m+2*u)
        have hproduct := QInterval.mul_containsReal hc hp
        convert hproduct using 1
        · simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
            Rat.cast_natCast, Rat.cast_ofNat,
            Rat.cast_neg, Rat.cast_one]
          rw [pow_add, pow_mul]
          ring
      · simp only [if_neg hmk, mul_zero]
        simpa only [Rat.cast_zero] using
          (thetaRationalPoint_containsReal (0:ℚ)))

/-- The entire 5x5 candidate interval matrix encloses the
TRUE first square-index theta summand, not a sampled proxy. -/
theorem thetaSecondCellCubicFirstSquareMatrix_containsReal
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaSecondCellCubicFirstSquareMatrix i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
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
  have haxQ : ((1/8:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hax
  have hxbQ : x ≤ ((177/512:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx hx1 i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox (1/8) (177/512))
    (thetaSecondCellCubicBinomialCoefficientBox i j)
    (thetaNthCubicGammaMomentBox (1/8) (177/512) 1)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal
      (1/8) (177/512) x haxQ hxbQ)
    (fun k _ =>
      thetaSecondCellCubicBinomialCoefficientBox_containsReal
        x hax hxb i j k)
    (fun k _ => by
      simpa only [Nat.cast_one, div_one] using
        (thetaNthCubicGammaMomentBox_containsReal
          (1/8) (177/512) x
          (by norm_num) haxQ hxbQ
          (by norm_num) 1 k (by omega)))

end W5
