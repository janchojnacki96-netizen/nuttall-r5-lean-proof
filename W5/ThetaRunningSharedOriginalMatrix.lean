import W5.ThetaGammaSharedRunningNine
import W5.ThetaRunningOriginalMatrix

/-!
# Reuse all nine cached root-grid Gamma moments in the ORIGINAL theta 5x5 matrix

The proved nine-moment vector evaluator is used for the genuine n=1
and n=2 Gaussian correction terms. We establish EXACT equality, entry
by entry, with the already-verified thetaRunningBothCellMatrix.

This is an implementation optimization, not a new theta model.
The n>=3 correction terms and n>=7 tail are completely unchanged.
No numerical test is asserted true, and no analytic theorem is assumed.
-/

namespace W5

/-- Selective n=1 moments: share root grids among k<9, and use the
already proved coarse moments for all degrees outside K. -/
def thetaRunningSharedSelectedNine
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ℕ → QInterval :=
  let sharp := thetaGammaRunningCellNine steps a b 1 us
  fun k =>
    if hk : k < 9 then
      if k ∈ K then sharp ⟨k, hk⟩
      else thetaNthCubicGammaMomentBox a b 1 k
    else thetaGammaRunningSelectedMomentBox steps a b us K k

theorem thetaRunningSharedSelectedNine_eq
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) :
    thetaRunningSharedSelectedNine steps a b us K k =
      thetaGammaRunningSelectedMomentBox steps a b us K k := by
  by_cases hk : k < 9
  · by_cases hK : k ∈ K
    · simp [thetaRunningSharedSelectedNine,
        thetaGammaRunningSelectedMomentBox, hk, hK,
        thetaGammaRunningCellNine_apply]
    · simp [thetaRunningSharedSelectedNine,
        thetaGammaRunningSelectedMomentBox, hk, hK]
  · simp [thetaRunningSharedSelectedNine, hk]

def thetaRunningSharedFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ThetaIntervalMatrix :=
  let M := thetaRunningSharedSelectedNine steps a b us K
  Matrix.of (fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      M 9)

theorem thetaRunningSharedFirstSquareMatrix_apply
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (i j : Fin 5) :
    thetaRunningSharedFirstSquareMatrix steps a b us K i j =
      thetaRunningFirstSquareMatrix steps a b us K i j := by
  have hM : thetaRunningSharedSelectedNine steps a b us K =
      thetaGammaRunningSelectedMomentBox steps a b us K := by
    funext k
    exact thetaRunningSharedSelectedNine_eq steps a b us K k
  simp only [thetaRunningSharedFirstSquareMatrix,
    thetaRunningFirstSquareMatrix, Matrix.of_apply, hM]

/-- n=2 moments use the same cached nine-moment vector for their
common x/2 endpoint grids, instead of repeating root computation. -/
def thetaRunningSharedAutoNine
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) : ℕ → QInterval :=
  let M := thetaGammaRunningCellNine steps a b n us
  fun k =>
    if hk : k < 9 then M ⟨k, hk⟩
    else thetaGammaRunningRoundedCellMomentBox steps k a b n us

theorem thetaRunningSharedAutoNine_eq
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (k : ℕ) :
    thetaRunningSharedAutoNine steps a b n us k =
      thetaRunningAutoNine steps a b n us k := by
  calc
    thetaRunningSharedAutoNine steps a b n us k =
        thetaGammaRunningRoundedCellMomentBox steps k a b n us := by
          by_cases hk : k < 9
          · simp [thetaRunningSharedAutoNine, hk,
              thetaGammaRunningCellNine_apply]
          · simp [thetaRunningSharedAutoNine, hk]
    _ = thetaRunningAutoNine steps a b n us k :=
      (thetaRunningAutoNine_eq steps a b n us k).symm

def thetaRunningSharedN2Matrix
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let E := thetaBulkFixedGaussianExpBox a b 2
  let M := thetaRunningSharedAutoNine steps a b 2 us
  Matrix.of (fun i j =>
    thetaBulkSignedParameterizedTermBox a b 2 i j E M)

theorem thetaRunningSharedN2Matrix_apply
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) (i j : Fin 5) :
    thetaRunningSharedN2Matrix steps us a b i j =
      thetaRunningN2Matrix steps us a b i j := by
  have hM : thetaRunningSharedAutoNine steps a b 2 us =
      thetaRunningAutoNine steps a b 2 us := by
    funext k
    exact thetaRunningSharedAutoNine_eq steps a b 2 us k
  simp only [thetaRunningSharedN2Matrix,
    thetaRunningN2Matrix, Matrix.of_apply, hM]

/-- New original genuine theta matrix: no mathematical changes.
The two dominant square-index terms use shared fourth-root grids. -/
def thetaRunningSharedBothCellMatrix
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N1 := thetaRunningSharedFirstSquareMatrix steps a b us K
  let N2 := thetaRunningSharedN2Matrix steps us a b
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaRunningBothTermBox N1 N2 a b i j))
      thetaBulkSevenTailBox)

theorem thetaRunningSharedBothCellMatrix_eq
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) :
    thetaRunningSharedBothCellMatrix steps us K a b =
      thetaRunningBothCellMatrix steps us K a b := by
  have hN1 : thetaRunningSharedFirstSquareMatrix steps a b us K =
      thetaRunningFirstSquareMatrix steps a b us K := by
    funext i j
    exact thetaRunningSharedFirstSquareMatrix_apply steps a b us K i j
  have hN2 : thetaRunningSharedN2Matrix steps us a b =
      thetaRunningN2Matrix steps us a b := by
    funext i j
    exact thetaRunningSharedN2Matrix_apply steps us a b i j
  simp only [thetaRunningSharedBothCellMatrix,
    thetaRunningBothCellMatrix, hN1, hN2]

/-- All rational enclosure comparisons are now made with the faster
exactly equal source; reuse existing real-theta soundness verbatim. -/
def thetaRunningSharedCellAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b) &&
  thetaUpperMatrixRefinesCheck target
    (thetaRunningSharedBothCellMatrix steps us K a b)

theorem thetaRunningSharedCellAuditCheck_eq
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) :
    thetaRunningSharedCellAuditCheck steps us K target a b =
      thetaRunningBothCellAuditCheck steps us K target a b := by
  simp only [thetaRunningSharedCellAuditCheck,
    thetaRunningBothCellAuditCheck,
    thetaRunningSharedBothCellMatrix_eq]

end W5
