import W5.ThetaAuditedMomentGammaBox
import W5.ThetaRealPivotProductSigns

/-!
# A small all-rational first-cell candidate certificate

The existing Mathlib Gamma enclosure gives rational intervals for
all nine TRUE weighted moments without any external numerical integration.
Here we use a deliberately WIDE and simple rational enclosure
  |coeff_k(B_ij(wx,1+w*x²))| <= 4 / 8^k,  0 < x <= 1/8.
We DO NOT assert this last analytic inequality as a proved theorem.
It is packaged as a named, explicit missing obligation.

Once the coefficient inequality is supplied, the imported real
interval-soundness and exact five-pivot LDL checker certify all five
real pivot signs for the true first-cell theta matrix.

The finite rational candidate can be checked independently by
native_decide, without reproducing the 768-bit auditor's 51 matrices.
-/

namespace W5

/-- The only missing analytic statement for this alternative compact
first-cell candidate: a uniform bound on each of the nine true
polynomial coefficients. This is NOT currently a theorem. -/
def ThetaFirstCellGammaUniformCoefficientBound : Prop :=
  ∀ x : ℝ, 0 < x → x ≤ (1 : ℝ)/8 →
    ∀ i j : Fin 5, ∀ k ∈ Finset.range 9,
      |(thetaCorrectionWPolynomial x 1 0 i j).coeff k| ≤
        (4 : ℝ) / (8 : ℝ)^k

/-- One exact-rational enclosure used for all 25 entries and k. -/
def thetaFirstCellGammaUniformCoeffBox (k : ℕ) : QInterval :=
  ⟨-(4 / (8 : ℚ)^k), 4 / (8 : ℚ)^k⟩

/-- The original n=1 diagonal is EXACTLY rational (not an interval
approximation). -/
def thetaFirstCellGammaUniformDiagonal (i j : Fin 5) : QInterval :=
  ⟨if i = j then (-1 : ℚ)^i.val / (Nat.factorial i.val : ℚ) else 0,
   if i = j then (-1 : ℚ)^i.val / (Nat.factorial i.val : ℚ) else 0⟩

/-- For 0<=x<=1/8, 0<=x²/4<=1/256. -/
def thetaFirstCellGammaUniformScale : QInterval :=
  ⟨0, 1 / 256⟩

/-- The first-cell candidate is one uniform nine-moment rational
interval expression plus the already proved 10^(-35) true tail. -/
def thetaFirstCellGammaUniformMatrix : ThetaIntervalMatrix :=
  fun i j =>
    QInterval.add
      (thetaAuditedOneTermMomentInterval
        (thetaFirstCellGammaUniformDiagonal i j)
        thetaFirstCellGammaUniformScale
        thetaFirstCellGammaUniformCoeffBox
        thetaAuditedFirstCellGammaMomentInterval 9)
      thetaAuditedTailErrorInterval

/-- Purely FINITE certified computation: the five original
alternating LDL signs all hold for this WIDE rational matrix.
This uses the pre-existing intervalLDL5AlternatingCheck, not a
new algorithm or a floating-point test. -/
theorem thetaFirstCellGammaUniformMatrix_checked :
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals thetaFirstCellGammaUniformMatrix) = true := by
  native_decide

theorem thetaFirstCellGammaUniformMatrix_pivotSigns :
    intervalLDL5Alternating
      (thetaSymmetricIntervals thetaFirstCellGammaUniformMatrix) := by
  exact intervalLDL5Alternating_of_check
    (thetaSymmetricIntervals thetaFirstCellGammaUniformMatrix)
    thetaFirstCellGammaUniformMatrix_checked

/-- Under the one explicit, still-open bound on genuine
polynomial coefficients, all 15 TRUE theta entries are enclosed
on the first cell by this new exact-rational matrix. -/
theorem thetaFirstCellGammaUniformMatrix_containsReal
    (hcoeff : ThetaFirstCellGammaUniformCoefficientBound)
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaFirstCellGammaUniformMatrix i j)
      (thetaCoefficient x i j) := by
  have hD : QInterval.ContainsReal
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
  have hsq : x^2 ≤ (1 : ℝ)/64 := by
    have hprod : 0 ≤ ((1 : ℝ)/8-x) * ((1 : ℝ)/8+x) := by
      apply mul_nonneg
      · linarith
      · linarith
    nlinarith
  have hX : QInterval.ContainsReal
      thetaFirstCellGammaUniformScale (x^2/4) := by
    have hp : (0 : ℝ) ≤ x^2/4 ∧
        x^2/4 ≤ (1 : ℝ)/256 := by
      constructor
      · positivity
      · nlinarith
    simpa [thetaFirstCellGammaUniformScale,
      QInterval.ContainsReal] using hp
  have hC : ∀ k ∈ Finset.range 9,
      QInterval.ContainsReal (thetaFirstCellGammaUniformCoeffBox k)
        ((thetaCorrectionWPolynomial x 1 0 i j).coeff k) := by
    intro k hk
    have hreal := abs_le.mp (hcoeff x hx hxB i j k hk)
    simpa only [thetaFirstCellGammaUniformCoeffBox,
      QInterval.ContainsReal, Rat.cast_neg,
      Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using hreal
  exact thetaCoefficient_first_cell_containsReal_of_gamma_box
    x hx hxB i j
    (thetaFirstCellGammaUniformDiagonal i j)
    thetaFirstCellGammaUniformScale
    thetaFirstCellGammaUniformCoeffBox
    (thetaFirstCellGammaUniformMatrix i j)
    hD hX hC
    (by dsimp [thetaFirstCellGammaUniformMatrix]; exact le_rfl)
    (by dsimp [thetaFirstCellGammaUniformMatrix]; exact le_rfl)

/-- This is the complete, explicitly CONDITIONAL first-cell
real-matrix LDL sign result. The expensive finite rational check
and all integrability/tail/Gamma inputs are discharged; only the
uniform true polynomial coefficient inequality remains. -/
theorem thetaFirstCellGammaUniform_realPivotSigns
    (hcoeff : ThetaFirstCellGammaUniformCoefficientBound)
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  have hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal
        (thetaSymmetricIntervals thetaFirstCellGammaUniformMatrix i j)
        (thetaCoefficient x i j) := by
    intro i j
    exact thetaSymmetricIntervals_contains_theta
      thetaFirstCellGammaUniformMatrix x
      (fun a b _ =>
        thetaFirstCellGammaUniformMatrix_containsReal
          hcoeff x hx hxB a b) i j
  exact thetaFive_pivotSigns_of_interval
    x (thetaSymmetricIntervals thetaFirstCellGammaUniformMatrix)
    hentry thetaFirstCellGammaUniformMatrix_pivotSigns

end W5
