import W5.ThetaSecondCellCubicFirstSquareReal
import W5.ThetaSecondCellCubicWidenedLDL
import W5.ThetaSecondCellHeadFiniteMajorants

/-!
# Generic cubic-Gamma interval matrix and the next 51-cell candidate

Rather than duplicate the second-cell proof 49 times, generalize the
existing exact finite binomial coefficient formula and its real-sound
Gamma integration to arbitrary rational x-cells [a,b]. This one generic
module can be reused for every remaining cell.

Cell 3 uses the *same verified* QInterval 5-pivot checker and a uniform
1/100 tail allowance. Its true n>=2 tail remains a separate obligation:
a finite rational LDL check alone is not a genuine analytic certificate.
-/

namespace W5

/-- A fully computable rational expression for the exact w-polynomial
coefficients of the ORIGINAL n=1 theta integral on any x-cell. -/
def thetaGeneralCellCubicBinomialCoefficientBox
    (a b : ℚ) (i j : Fin 5) (k : ℕ) : QInterval :=
  QInterval.finsetSum (Finset.range (min i.val j.val + 1))
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
          (QInterval.pow (⟨a,b⟩ : QInterval) (m+2*u))
      else QInterval.point 0)

/-- The generic computable expression specializes definitionally to
the CI-green second-cell coefficient calculator. -/
theorem thetaGeneralCellCubicBinomialCoefficientBox_second
    (i j : Fin 5) (k : ℕ) :
    thetaGeneralCellCubicBinomialCoefficientBox
      (1/8) (177/512) i j k =
        thetaSecondCellCubicBinomialCoefficientBox i j k := by
  rfl

/-- A single real-soundness proof for all 25 polynomial entries and
arbitrary rational x-cells. The algebra is the existing verified
second-cell Mathlib binomial proof with endpoints generalized. -/
theorem thetaGeneralCellCubicBinomialCoefficientBox_containsReal
    (a b : ℚ) (x : ℝ) (hax : (a:ℝ) ≤ x)
    (hxb : x ≤ (b:ℝ))
    (i j : Fin 5) (k : ℕ) :
    QInterval.ContainsReal
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j k)
      ((thetaCorrectionWPolynomial x 1 0 i j).coeff k) := by
  have hxBox : QInterval.ContainsReal
      (⟨a,b⟩ : QInterval) x := ⟨hax, hxb⟩
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
          (QInterval.pow (⟨a,b⟩ : QInterval) (m+2*u))
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
            (QInterval.pow (⟨a,b⟩ : QInterval) (m+2*u))
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
            (⟨a,b⟩ : QInterval) x hxBox (m+2*u)
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


/-- Computable n=1 cubic-Gamma interval matrix for any rational cell. -/
def thetaGeneralCellCubicFirstSquareMatrix
    (a b : ℚ) : ThetaIntervalMatrix :=
  fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      (thetaNthCubicGammaMomentBox a b 1) 9

/-- The generic construction is *definitionally identical* to the existing
CI-green cell-2 matrix, avoiding a second implementation of the checker. -/
theorem thetaGeneralCellCubicFirstSquareMatrix_second :
    thetaGeneralCellCubicFirstSquareMatrix (1/8) (177/512) =
      thetaSecondCellCubicFirstSquareMatrix := by
  rfl

/-- The computable generic first-square matrix contains the ORIGINAL
theta n=1 term on every nonnegative rational x-cell with b≤1.
Reuse the existing moment, polynomial, scale and interval-sum proofs. -/
theorem thetaGeneralCellCubicFirstSquareMatrix_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ)) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1) (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaGeneralCellCubicFirstSquareMatrix a b i j)
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
    (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
    (thetaNthCubicGammaMomentBox a b 1)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaGeneralCellCubicBinomialCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ => by
      simpa only [Nat.cast_one, div_one] using
        (thetaNthCubicGammaMomentBox_containsReal
          a b x ha hax hxb hb1 1 k (by omega)))

/-- Generic 1/100-width tail allowance. The only cell-specific work
is a finite LDL check and the actual n>=2 analytic tail inequality. -/
def thetaGeneralCellCubicWidenedMatrix
    (a b : ℚ) : ThetaIntervalMatrix :=
  fun i j =>
    QInterval.add
      (thetaGeneralCellCubicFirstSquareMatrix a b i j)
      thetaSecondCellUniformTailAllowance

/-- All 25 genuine theta entries are enclosed by the same fully
computable cubic-Gamma matrix, conditioned solely on an actual n>=2 tail. -/
theorem thetaGeneralCellCubicWidenedMatrix_containsReal_of_tail
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ)) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (htail : ∀ i j : Fin 5,
      |thetaAuditedTail 2 x i j| ≤ (1:ℝ)/100)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaGeneralCellCubicWidenedMatrix a b i j)
      (thetaCoefficient x i j) := by
  have hOne := thetaGeneralCellCubicFirstSquareMatrix_containsReal
    a b x ha hx hax hxb hb1 i j
  have hTail : QInterval.ContainsReal
      thetaSecondCellUniformTailAllowance (thetaAuditedTail 2 x i j) := by
    have h := abs_le.mp (htail i j)
    simpa [thetaSecondCellUniformTailAllowance,
      QInterval.ContainsReal, div_eq_mul_inv] using h
  have hSplit :
      thetaCoefficient x i j =
        thetaAuditedSeriesTerm x i j 1 + thetaAuditedTail 2 x i j := by
    rw [thetaCoefficient_eq_audited_prefix_add_tail_unconditional
      2 x hx (hxb.trans hb1) i j]
    rw [thetaAuditedPrefix_two_eq_one]
  rw [hSplit]
  exact QInterval.add_containsReal hOne hTail

/-- The THIRD audited interval from the original 51-cell list. -/
def thetaThirdCellCubicWidenedMatrix : ThetaIntervalMatrix :=
  thetaGeneralCellCubicWidenedMatrix (177/512) (821/2048)

/-- Verify the third interval endpoint comes directly from the ORIGINAL
audited list, not a new approximate partition. -/
theorem thetaThirdCell_endpoint :
    endpoints.drop 2 = (821/2048:ℚ) :: endpoints.drop 3 := by
  native_decide

/-- Independent rational LDL check for the third interval, using
the same exact checker as the first two cells. -/
theorem thetaThirdCellCubicWidenedMatrix_checked :
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaThirdCellCubicWidenedMatrix) = true := by
  native_decide

theorem thetaThirdCellCubicWidenedMatrix_pivotSigns :
    intervalLDL5Alternating
      (thetaSymmetricIntervals thetaThirdCellCubicWidenedMatrix) := by
  exact intervalLDL5Alternating_of_check
    (thetaSymmetricIntervals thetaThirdCellCubicWidenedMatrix)
    thetaThirdCellCubicWidenedMatrix_checked

/-- Concrete exact-rational K bounds for the n=2,3,4 original
theta head terms on cell 3, uniformly across all 25 matrix entries. -/
theorem thetaThirdCellHeadPositiveMajorants_checked :
    ∀ i j : Fin 5,
      thetaHeadPositiveMajorant (177/512) (821/2048) 2 i j ≤
        (500000:ℚ) ∧
      thetaHeadPositiveMajorant (177/512) (821/2048) 3 i j ≤
        (2000000000:ℚ) ∧
      thetaHeadPositiveMajorant (177/512) (821/2048) 4 i j ≤
        (400000000000:ℚ) := by
  native_decide

/-- Full actual real third-cell five-pivot signs reduce to a single
n>=2 original theta tail inequality; no determinant work remains. -/
theorem thetaThirdCell_allFivePivotSigns_of_tail
    (x : ℝ) (hax : (177:ℝ)/512 ≤ x)
    (hxb : x ≤ (821:ℝ)/2048)
    (htail : ∀ i j : Fin 5,
      |thetaAuditedTail 2 x i j| ≤ (1:ℝ)/100) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  have ha : ((177/512:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hax
  have hb : x ≤ ((821/2048:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal
        ((thetaSymmetricIntervals thetaThirdCellCubicWidenedMatrix) i j)
        (thetaCoefficient x i j) := by
    intro i j
    exact thetaSymmetricIntervals_contains_theta
      thetaThirdCellCubicWidenedMatrix x
      (fun k l _ =>
        thetaGeneralCellCubicWidenedMatrix_containsReal_of_tail
          (177/512) (821/2048) x
          (by norm_num) hx ha hb (by norm_num) htail k l) i j
  exact thetaFive_pivotSigns_of_interval x
    (thetaSymmetricIntervals thetaThirdCellCubicWidenedMatrix)
    hentry thetaThirdCellCubicWidenedMatrix_pivotSigns

end W5
