import W5.ThetaGammaDegreeSelectedMoments
import W5.ThetaGammaMemoNine

/-!
# Share exact k-selective Gamma moments across the n=1 theta matrix

The n=1 original theta term is evaluated for 15 independent matrix
entries, but all 15 consume the SAME nine moment intervals. The
existing k-selective generator can recompute the rational Gamma grid
dozens of times in one 5x5 matrix. Here one 9-element array is built
for that cell and shared across all coefficients.

Its values are EXACTLY those of the original proved real-sound
k-selective moment oracle, including all k beyond 8. The real-sound
entry theorem below is imported, not reproved.
-/

namespace W5

def thetaGammaMemoDegreeSelectedNine
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ℕ → QInterval :=
  let cached : Array QInterval :=
    Array.ofFn (fun k : Fin 9 =>
      thetaGammaDegreeSelectedMomentBox steps a b us K k.val)
  fun k =>
    if hk : k < 9 then
      cached[k]'(by simpa [cached] using hk)
    else thetaGammaDegreeSelectedMomentBox steps a b us K k

theorem thetaGammaMemoDegreeSelectedNine_eq
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) :
    thetaGammaMemoDegreeSelectedNine steps a b us K k =
      thetaGammaDegreeSelectedMomentBox steps a b us K k := by
  by_cases hk : k < 9
  · simp [thetaGammaMemoDegreeSelectedNine, hk]
  · simp [thetaGammaMemoDegreeSelectedNine, hk]

/-- A closure over one moment array, reused by all 25 original
coefficients. Does not change rounding, coefficients or Gamma grid. -/
def thetaGammaMemoDegreeSelectedFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ThetaIntervalMatrix :=
  let M := thetaGammaMemoDegreeSelectedNine steps a b us K
  Matrix.of (fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      M 9)

/-- No separate numerical or analytic argument: exactly the same
QInterval is returned for each i,j as by the original evaluator. -/
theorem thetaGammaMemoDegreeSelectedFirstSquareMatrix_apply
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (i j : Fin 5) :
    thetaGammaMemoDegreeSelectedFirstSquareMatrix
      steps a b us K i j =
      thetaGammaDegreeSelectedFirstSquareMatrix
        steps a b us K i j := by
  have hM : thetaGammaMemoDegreeSelectedNine steps a b us K =
      thetaGammaDegreeSelectedMomentBox steps a b us K := by
    funext k
    exact thetaGammaMemoDegreeSelectedNine_eq
      steps a b us K k
  simp only [thetaGammaMemoDegreeSelectedFirstSquareMatrix,
    thetaGammaDegreeSelectedFirstSquareMatrix,
    Matrix.of_apply, hM]

theorem thetaGammaMemoDegreeSelectedFirstSquareMatrix_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaGammaMemoDegreeSelectedFirstSquareMatrix
        steps a b us K i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  rw [thetaGammaMemoDegreeSelectedFirstSquareMatrix_apply]
  exact thetaGammaDegreeSelectedFirstSquareMatrix_containsReal
    steps a b us K x ha hx hax hxb hb hA hB i j

end W5
