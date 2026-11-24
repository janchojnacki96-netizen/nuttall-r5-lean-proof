import W5.ThetaGammaMemoNine
import W5.ThetaBulkDegreeSelectedGammaCells

/-!
# Memoized exact n=2 source for arbitrary original theta x-subcells

The generic n/k-selected generator already proves genuine REAL
enclosures, but its exact-rational n=2 correction formula asks for
the same expensive nine Gamma moments many times across the 5x5
matrix. The canonical nine-moment cache proved entrywise equality
to the original generator. Here the cached n=2 matrix is constructed
ONCE and shared across all 25 coefficients and the finite prefix.

The proofs below show literal equality of EVERY generated interval
to the existing, already verified S={2} generator. No new analytic
hypotheses, LDL evaluations, or acceptance of a numerical certificate.
-/

namespace W5

/-- Reuse the already proven sharp n=2 memoized matrix at a single
square index; all other original signed terms are unchanged. -/
def thetaMemoN2SelectedTermBox
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 2 then
    thetaBulkMemoSharpHigherSquareMatrix steps us a b 2 i j
  else
    thetaBulkDegreeSelectedTermBox
      steps us K ({2} : Finset ℕ) a b i j n

/-- The memoized term equals the genuine original certified term
for all n, not only for the special n=2 case. -/
theorem thetaMemoN2SelectedTermBox_eq
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) :
    thetaMemoN2SelectedTermBox steps us K a b i j n =
      thetaBulkDegreeSelectedTermBox
        steps us K ({2} : Finset ℕ) a b i j n := by
  by_cases hn : n = 2
  · subst n
    simp only [thetaMemoN2SelectedTermBox, ↓reduceIte]
    rw [thetaBulkMemoSharpHigherSquareMatrix_apply]
    simp [thetaBulkDegreeSelectedTermBox,
      thetaBulkSelectedGammaTermBox]
  · simp [thetaMemoN2SelectedTermBox, hn]

/-- The n=2 matrix and all nine of its moments are let-bound
before the 25-entry matrix is assembled. This is a computational
sharing optimization only: the formulas and endpoints remain exact. -/
def thetaMemoN2SelectedCellMatrix
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N2 := thetaBulkMemoSharpHigherSquareMatrix steps us a b 2
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (fun n => if n = 2 then N2 i j
          else thetaBulkDegreeSelectedTermBox
            steps us K ({2} : Finset ℕ) a b i j n))
      thetaBulkSevenTailBox)

/-- Exact entrywise equality of the optimized source to the
already-certified n/k selected source with sharp n=2. -/
theorem thetaMemoN2SelectedCellMatrix_apply
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) (i j : Fin 5) :
    thetaMemoN2SelectedCellMatrix steps us K a b i j =
      thetaBulkDegreeSelectedCellMatrix
        steps us K ({2} : Finset ℕ) a b i j := by
  have hfun :
      (fun n => if n = 2 then
          thetaBulkMemoSharpHigherSquareMatrix steps us a b 2 i j
        else thetaBulkDegreeSelectedTermBox
          steps us K ({2} : Finset ℕ) a b i j n) =
      (thetaBulkDegreeSelectedTermBox
        steps us K ({2} : Finset ℕ) a b i j) := by
    funext n
    exact thetaMemoN2SelectedTermBox_eq
      steps us K a b i j n
  change
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (fun n => if n = 2 then
          thetaBulkMemoSharpHigherSquareMatrix steps us a b 2 i j
         else thetaBulkDegreeSelectedTermBox
          steps us K ({2} : Finset ℕ) a b i j n))
      thetaBulkSevenTailBox =
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkDegreeSelectedTermBox
          steps us K ({2} : Finset ℕ) a b i j))
      thetaBulkSevenTailBox
  rw [hfun]

/-- The actual theta coefficient is contained in every cached
entry: reuse the exact proven REAL semantics of the canonical
S={2} generator without duplicating any Gamma integral proof. -/
theorem thetaMemoN2SelectedCellMatrix_containsReal
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
      (thetaMemoN2SelectedCellMatrix steps us K a b i j)
      (thetaCoefficient x i j) := by
  rw [thetaMemoN2SelectedCellMatrix_apply]
  exact thetaBulkDegreeSelectedCellMatrix_containsReal
    steps us K ({2} : Finset ℕ) a b x
    ha hx hax hxb hb hExp hA hB hSel i j

end W5
