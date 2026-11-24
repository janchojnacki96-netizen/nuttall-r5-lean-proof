import W5.ThetaRunningMaterializedNine
import W5.ThetaFiniteDecidableLDLChecker

/-!
# Direct five-pivot certification with the verified Gamma generator

No containment in an imported audit matrix is required. Use the
actual real-sound generated matrix, complete it symmetrically,
materialize the entries and run the already proved signed LDL
interval test. All cached matrices are exactly equal to the old
Schur matrices; no numerical rounding or new analytic premise.
-/

namespace W5

def thetaDirectCacheFive {α : Type} (f : Fin 5 → α) : Fin 5 → α :=
  let cached : Array α := Array.ofFn f
  fun i => cached[i.val]'(by simpa [cached] using i.isLt)

theorem thetaDirectCacheFive_apply {α : Type} (f : Fin 5 → α)
    (i : Fin 5) : thetaDirectCacheFive f i = f i := by
  simp [thetaDirectCacheFive]

def thetaDirectCacheMatrix (B : ThetaIntervalMatrix) : ThetaIntervalMatrix :=
  Matrix.of (thetaDirectCacheFive (fun i => thetaDirectCacheFive (B i)))

theorem thetaDirectCacheMatrix_eq (B : ThetaIntervalMatrix) :
    thetaDirectCacheMatrix B = B := by
  ext i j
  simp only [thetaDirectCacheMatrix, Matrix.of_apply,
    thetaDirectCacheFive_apply]

/-- Materialize each Schur stage so repeated entries do not recursively
reevaluate the previous stages or the expensive original theta matrix. -/
def thetaDirectCachedLDL (B : ThetaIntervalMatrix) :
    ℕ → ThetaIntervalMatrix
  | 0 => thetaDirectCacheMatrix B
  | k+1 => thetaDirectCacheMatrix
      (intervalSchurStep (thetaDirectCachedLDL B k) (pivotIndexFive k))

theorem thetaDirectCachedLDL_eq (B : ThetaIntervalMatrix) (k : ℕ) :
    thetaDirectCachedLDL B k = intervalLDL5 B k := by
  induction k with
  | zero => simp only [thetaDirectCachedLDL, intervalLDL5,
      thetaDirectCacheMatrix_eq]
  | succ k ih =>
      simp only [thetaDirectCachedLDL, intervalLDL5,
        thetaDirectCacheMatrix_eq, ih]

def thetaDirectPivot (B : ThetaIntervalMatrix) (k : ℕ) : QInterval :=
  thetaDirectCachedLDL B k (pivotIndexFive k) (pivotIndexFive k)

def thetaDirectLDLCheck (B : ThetaIntervalMatrix) : Bool :=
  decide (0 < (thetaDirectPivot B 0).lo) &&
  decide ((thetaDirectPivot B 1).hi < 0) &&
  decide (0 < (thetaDirectPivot B 2).lo) &&
  decide ((thetaDirectPivot B 3).hi < 0) &&
  decide (0 < (thetaDirectPivot B 4).lo)

theorem thetaDirectLDLCheck_eq (B : ThetaIntervalMatrix) :
    thetaDirectLDLCheck B = intervalLDL5AlternatingCheck B := by
  simp only [thetaDirectLDLCheck, thetaDirectPivot,
    thetaDirectCachedLDL_eq, intervalLDL5AlternatingCheck]

def thetaDirectCellCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : Bool :=
  thetaRunningCellEligible steps us a b &&
    thetaDirectLDLCheck (thetaSymmetricIntervals
      (thetaRunningMaterializedBothCellMatrix steps us K a b))

/-- Direct success proves the genuine theta-cell certificate,
without A44/A34 or any other imported target-box comparisons. -/
theorem thetaDirectCellCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ) (a b : ℚ)
    (h : thetaDirectCellCheck steps us K a b = true) :
    ThetaUpperRealCellCertificate a b := by
  have hh :
      ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
        ThetaBulkGaussianEligibility a b ∧
        thetaGammaAutoMomentCheck steps a us = true ∧
        thetaGammaAutoMomentCheck steps b us = true ∧
        ThetaBulkSelectedGammaEligibility steps us ({2} : Finset ℕ) a b) ∧
      intervalLDL5AlternatingCheck (thetaSymmetricIntervals
        (thetaRunningMaterializedBothCellMatrix steps us K a b)) = true := by
    simpa only [thetaDirectCellCheck, thetaRunningCellEligible,
      thetaDirectLDLCheck_eq, Bool.and_eq_true, decide_eq_true_eq] using h
  rcases hh with ⟨⟨ha, _, hb, hExp, hA, hB, hSel⟩, hldl⟩
  apply thetaUpperRealCellCertificate_of_checked a b
    (thetaRunningMaterializedBothCellMatrix steps us K a b) hldl
  intro x hx hax hxb i j _
  have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  rw [thetaRunningMaterializedBothCellMatrix_eq]
  exact thetaRunningBothCellMatrix_containsReal
    steps us K a b x ha hx hax hxb hbR hExp hA hB hSel i j

/-- The direct certificate works on arbitrary endpoint chains. -/
def thetaDirectChainCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ) : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs => thetaDirectCellCheck steps us K a b &&
      thetaDirectChainCheck steps us K b bs

theorem thetaDirectChainCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ) (bs : List ℚ) :
    ∀ a : ℚ, thetaDirectChainCheck steps us K a bs = true →
      ThetaUpperRealCellCertificateChain a bs := by
  induction bs with
  | nil => intro a _; trivial
  | cons b bs ih =>
      intro a h
      have hh : thetaDirectCellCheck steps us K a b = true ∧
          thetaDirectChainCheck steps us K b bs = true := by
        simpa only [thetaDirectChainCheck, Bool.and_eq_true] using h
      exact ⟨thetaDirectCellCheck_sound steps us K a b hh.1, ih b hh.2⟩

theorem analyticMatrixPositive_of_direct48
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (h : thetaDirectChainCheck steps us K (821/2048:ℚ)
      (endpoints.drop 3) = true) : analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaDirectChainCheck_sound steps us K (endpoints.drop 3)
      (821/2048:ℚ) h)

end W5
