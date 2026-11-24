import W5.ThetaMemoN2SelectedCellMatrix
import W5.ThetaGammaMemoDegreeSelectedNine

/-!
# Memoize BOTH dominant original theta terms across one x-cell

The original 5x5 theta coefficient generator uses the SAME nine
Gamma moments for all entries at n=1 and at n=2. Both moment arrays
are cached and shared by this cell source, while n=3..6 are unchanged.

Every returned QInterval is PROVED identical to the canonical
k-selected / S={2} generated interval. Accordingly all old sound
real-semantic and Schur-pivot transfer theorems apply without new
analytic assumptions, rounding approximations or numerical axioms.
-/

namespace W5

/-- Both expensive arrays are constructed once per cell, then
shared among every coefficient in its original 7-term prefix. -/
def thetaMemoN1N2SelectedCellMatrix
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N1 := thetaGammaMemoDegreeSelectedFirstSquareMatrix
    steps a b us K
  let N2 := thetaBulkMemoSharpHigherSquareMatrix
    steps us a b 2
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (fun n =>
          if n = 1 then N1 i j
          else if n = 2 then N2 i j
          else thetaBulkDegreeSelectedTermBox
            steps us K ({2} : Finset ℕ) a b i j n))
      thetaBulkSevenTailBox)

/-- Exact rational box equality, for all twenty-five entries and
all K, grids and x-cells. There is no loss of interval tightness. -/
theorem thetaMemoN1N2SelectedCellMatrix_apply
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) (i j : Fin 5) :
    thetaMemoN1N2SelectedCellMatrix steps us K a b i j =
      thetaBulkDegreeSelectedCellMatrix
        steps us K ({2} : Finset ℕ) a b i j := by
  have hfun :
      (fun n => if n = 1 then
          thetaGammaMemoDegreeSelectedFirstSquareMatrix
            steps a b us K i j
        else if n = 2 then
          thetaBulkMemoSharpHigherSquareMatrix
            steps us a b 2 i j
        else thetaBulkDegreeSelectedTermBox
          steps us K ({2} : Finset ℕ) a b i j n) =
      (thetaBulkDegreeSelectedTermBox
        steps us K ({2} : Finset ℕ) a b i j) := by
    funext n
    by_cases h1 : n = 1
    · subst n
      simp only [if_pos rfl]
      rw [thetaGammaMemoDegreeSelectedFirstSquareMatrix_apply]
      simp [thetaBulkDegreeSelectedTermBox]
    · have hn2 := thetaMemoN2SelectedTermBox_eq
        steps us K a b i j n
      simpa [thetaMemoN2SelectedTermBox, h1] using hn2
  change
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (fun n => if n = 1 then
          thetaGammaMemoDegreeSelectedFirstSquareMatrix
            steps a b us K i j
         else if n = 2 then
          thetaBulkMemoSharpHigherSquareMatrix
            steps us a b 2 i j
         else thetaBulkDegreeSelectedTermBox
          steps us K ({2} : Finset ℕ) a b i j n))
      thetaBulkSevenTailBox =
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkDegreeSelectedTermBox
          steps us K ({2} : Finset ℕ) a b i j))
      thetaBulkSevenTailBox
  rw [hfun]

/-- Formal real inclusion follows by rewriting with the previously
CI-certified original theta coefficient interval generator. -/
theorem thetaMemoN1N2SelectedCellMatrix_containsReal
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
      (thetaMemoN1N2SelectedCellMatrix steps us K a b i j)
      (thetaCoefficient x i j) := by
  rw [thetaMemoN1N2SelectedCellMatrix_apply]
  exact thetaBulkDegreeSelectedCellMatrix_containsReal
    steps us K ({2} : Finset ℕ) a b x
    ha hx hax hxb hb hExp hA hB hSel i j

end W5
