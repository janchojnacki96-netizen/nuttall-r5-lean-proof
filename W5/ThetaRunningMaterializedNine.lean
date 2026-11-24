import W5.ThetaRunningSharedOriginalMatrix
import W5.ThetaRunningSinglePassAuditGate

namespace W5

/-- Materialize all nine intervals, rather than repeatedly invoking a
closure for each matrix coefficient. -/
def thetaRunningMaterializedNine (M : ℕ → QInterval) : ℕ → QInterval :=
  let cached : Array QInterval := Array.ofFn (fun k : Fin 9 => M k.val)
  fun k =>
    if hk : k < 9 then cached[k]'(by simpa [cached] using hk)
    else M k

theorem thetaRunningMaterializedNine_apply (M : ℕ → QInterval) (k : ℕ) :
    thetaRunningMaterializedNine M k = M k := by
  by_cases hk : k < 9
  · simp [thetaRunningMaterializedNine, hk]
  · simp [thetaRunningMaterializedNine, hk]

def thetaRunningMaterializedFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ) (K : Finset ℕ) :
    ThetaIntervalMatrix :=
  let M := thetaRunningMaterializedNine
    (thetaRunningSharedSelectedNine steps a b us K)
  Matrix.of (fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      M 9)

theorem thetaRunningMaterializedFirstSquareMatrix_eq
    (steps : ℕ) (a b : ℚ) (us : List ℚ) (K : Finset ℕ) :
    thetaRunningMaterializedFirstSquareMatrix steps a b us K =
      thetaRunningSharedFirstSquareMatrix steps a b us K := by
  have hM : thetaRunningMaterializedNine
      (thetaRunningSharedSelectedNine steps a b us K) =
      thetaRunningSharedSelectedNine steps a b us K := by
    funext k
    exact thetaRunningMaterializedNine_apply _ k
  simp only [thetaRunningMaterializedFirstSquareMatrix,
    thetaRunningSharedFirstSquareMatrix, hM]

def thetaRunningMaterializedN2Matrix
    (steps : ℕ) (us : List ℚ) (a b : ℚ) : ThetaIntervalMatrix :=
  let E := thetaBulkFixedGaussianExpBox a b 2
  let M := thetaRunningMaterializedNine
    (thetaRunningSharedAutoNine steps a b 2 us)
  Matrix.of (fun i j =>
    thetaBulkSignedParameterizedTermBox a b 2 i j E M)

theorem thetaRunningMaterializedN2Matrix_eq
    (steps : ℕ) (us : List ℚ) (a b : ℚ) :
    thetaRunningMaterializedN2Matrix steps us a b =
      thetaRunningSharedN2Matrix steps us a b := by
  have hM : thetaRunningMaterializedNine
      (thetaRunningSharedAutoNine steps a b 2 us) =
      thetaRunningSharedAutoNine steps a b 2 us := by
    funext k
    exact thetaRunningMaterializedNine_apply _ k
  simp only [thetaRunningMaterializedN2Matrix,
    thetaRunningSharedN2Matrix, hM]

def thetaRunningMaterializedBothCellMatrix
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N1 := thetaRunningMaterializedFirstSquareMatrix steps a b us K
  let N2 := thetaRunningMaterializedN2Matrix steps us a b
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaRunningBothTermBox N1 N2 a b i j))
      thetaBulkSevenTailBox)

theorem thetaRunningMaterializedBothCellMatrix_eq
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ) (a b : ℚ) :
    thetaRunningMaterializedBothCellMatrix steps us K a b =
      thetaRunningBothCellMatrix steps us K a b := by
  rw [← thetaRunningSharedBothCellMatrix_eq steps us K a b]
  simp only [thetaRunningMaterializedBothCellMatrix,
    thetaRunningSharedBothCellMatrix,
    thetaRunningMaterializedFirstSquareMatrix_eq,
    thetaRunningMaterializedN2Matrix_eq]

def thetaRunningMaterializedSinglePassCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  thetaRunningCellEligible steps us a b &&
    (let source := thetaRunningMaterializedBothCellMatrix steps us K a b
     decide ((target 4 4).lo ≤ (source 4 4).lo ∧
       (source 4 4).hi ≤ (target 4 4).hi) &&
     (decide ((target 3 4).lo ≤ (source 3 4).lo ∧
       (source 3 4).hi ≤ (target 3 4).hi) &&
      thetaUpperMatrixRefinesCheck target source))

theorem thetaRunningMaterializedSinglePassCheck_eq
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) :
    thetaRunningMaterializedSinglePassCheck steps us K target a b =
      thetaRunningSinglePassAuditCheck steps us K target a b := by
  simp only [thetaRunningMaterializedSinglePassCheck,
    thetaRunningSinglePassAuditCheck,
    thetaRunningMaterializedBothCellMatrix_eq]

def thetaRunningMaterialized48Check
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ)) : Bool :=
  thetaGenericAuditedSubgridsCheck
    (thetaRunningMaterializedSinglePassCheck steps us K)
    (821/2048 : ℚ) (endpoints.drop 3)
    (thetaAuditUpperCellMatrices.drop 3) grids

theorem analyticMatrixPositive_of_materialized48
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ))
    (h : thetaRunningMaterialized48Check steps us K grids = true) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_audited_enclosures
  exact thetaGenericAuditedSubgridsCheck_sound
    (thetaRunningMaterializedSinglePassCheck steps us K)
    (fun target a b hc => by
      rw [thetaRunningMaterializedSinglePassCheck_eq] at hc
      exact thetaRunningSinglePassAuditCheck_sound steps us K target a b hc)
    (endpoints.drop 3) (821/2048 : ℚ)
    (thetaAuditUpperCellMatrices.drop 3) grids h

end W5
