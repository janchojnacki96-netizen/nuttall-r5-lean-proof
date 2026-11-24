import W5.ThetaEarlyRoundedGammaMoments
import W5.ThetaBulkDegreeSelectedGammaCells

/-!
# Genuine original theta coefficient matrix with early-rounded n1/n2

The existing certified theta generator delays rational rounding until
AFTER the expensive n=1 and n=2 signed Gamma expansions. This variant
uses the CI-proved early-rounded Gamma moment matrices for BOTH
dominant terms and leaves every n=3,...,6 signed correction and the
fully rigorous n>=7 infinite tail exactly unchanged.

The proof is the original seven-term real-enclosure reduction, not
an assumption about numerical coefficients or an LDL pivot result.
All 25 entries are uniformly sound on EVERY admissible x-cell.

This module is the intended fast numerical input for x-subdivision
tests, but does not assert that any inclusion check is true.
-/

namespace W5

/-- The original seven-term prefix: zero at n=0, early-rounded
true Gamma n=1 and n=2, old certified signed terms for n>=3. -/
def thetaEarlyRoundedBothTermBox
    (N1 N2 : ThetaIntervalMatrix) (a b : ℚ)
    (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else if n = 1 then N1 i j
  else if n = 2 then N2 i j
  else thetaBulkGeneratedSignedTerm a b i j n

/-- One shared pair of n=1/n=2 memo matrices is used for all
25 coefficient entries and the old n>=7 tail remains unchanged. -/
def thetaEarlyRoundedBothCellMatrix
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N1 := thetaEarlyRoundedFirstSquareMatrix steps a b us K
  let N2 := thetaEarlyRoundedN2Matrix steps us a b
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaEarlyRoundedBothTermBox N1 N2 a b i j))
      thetaBulkSevenTailBox)

/-- Soundness over REAL theta coefficients follows from the
two early-rounding lemmas and the already established original
n>=3 signed Gaussian envelope and uniform n>=7 tail bound. -/
theorem thetaEarlyRoundedBothCellMatrix_containsReal
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (hSel : ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaEarlyRoundedBothCellMatrix steps us K a b i j)
      (thetaCoefficient x i j) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal
        (thetaEarlyRoundedBothTermBox
          (thetaEarlyRoundedFirstSquareMatrix steps a b us K)
          (thetaEarlyRoundedN2Matrix steps us a b) a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [thetaEarlyRoundedBothTermBox,
        thetaAuditedSeriesTerm_zero, QInterval.ContainsReal,
        QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        simpa [thetaEarlyRoundedBothTermBox] using
          (thetaEarlyRoundedFirstSquareMatrix_containsReal
            steps a b us K x ha.le hx hax hxb hb1 hA hB i j)
      · by_cases hn2 : n = 2
        · subst n
          simpa [thetaEarlyRoundedBothTermBox] using
            (thetaEarlyRoundedN2Matrix_containsReal
              steps us a b x ha hx hax hxb hb
              hExp hSel i j)
        · have hn2lb : 2 ≤ n := by omega
          have hn7 : n < 7 := Finset.mem_range.mp hn
          simpa [thetaEarlyRoundedBothTermBox, hn0, hn1, hn2] using
            (thetaBulkGeneratedSignedTerm_containsReal
              a b x ha hx hax hxb hb hExp i j n hn2lb hn7)
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaEarlyRoundedBothTermBox
          (thetaEarlyRoundedFirstSquareMatrix steps a b us K)
          (thetaEarlyRoundedN2Matrix steps us a b) a b i j))
      thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j
    (thetaEarlyRoundedBothTermBox
      (thetaEarlyRoundedFirstSquareMatrix steps a b us K)
      (thetaEarlyRoundedN2Matrix steps us a b) a b i j)
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaEarlyRoundedBothTermBox
          (thetaEarlyRoundedFirstSquareMatrix steps a b us K)
          (thetaEarlyRoundedN2Matrix steps us a b) a b i j))
      thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- Exact-rational eligibility + original audited enclosure check
for a single x-cell; NO Schur LDL recomputation is necessary.
This is a Boolean diagnostic, not a certified numerical outcome. -/
def thetaEarlyRoundedBothCellAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b) &&
  thetaUpperMatrixRefinesCheck target
    (thetaEarlyRoundedBothCellMatrix steps us K a b)

/-- A successful executable Boolean means that the SAME audited
target matrix encloses every original REAL theta coefficient
throughout the specified cell. -/
theorem thetaEarlyRoundedBothCellAuditCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ)
    (hcheck : thetaEarlyRoundedBothCellAuditCheck
      steps us K target a b = true) :
    ∀ x : ℝ, 0 < x → (a:ℝ) ≤ x → x ≤ (b:ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j)
          (thetaCoefficient x i j) := by
  have hh :
      ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
        ThetaBulkGaussianEligibility a b ∧
        thetaGammaAutoMomentCheck steps a us = true ∧
        thetaGammaAutoMomentCheck steps b us = true ∧
        ThetaBulkSelectedGammaEligibility
          steps us ({2} : Finset ℕ) a b) ∧
      thetaUpperMatrixRefinesCheck target
        (thetaEarlyRoundedBothCellMatrix
          steps us K a b) = true := by
    simpa only [thetaEarlyRoundedBothCellAuditCheck,
      Bool.and_eq_true, decide_eq_true_eq] using hcheck
  rcases hh with ⟨⟨ha, _, hb, hExp, hA, hB, hSel⟩, hfit⟩
  intro x hx hax hxb i j hij
  have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
      exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact thetaUpperMatrixRefines_containsReal
    target (thetaEarlyRoundedBothCellMatrix steps us K a b)
    (thetaUpperMatrixRefinesCheck_sound _ _ hfit)
    (thetaCoefficient x i j) i j hij
    (thetaEarlyRoundedBothCellMatrix_containsReal
      steps us K a b x ha hx hax hxb hbR
      hExp hA hB hSel i j)

end W5
