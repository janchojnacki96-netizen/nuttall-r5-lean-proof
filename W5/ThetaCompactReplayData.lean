import W5.ThetaLastCellCompactDyadicWitness

/-!
# Reusable compact replay certificates for any of the 47 remaining cells

Only one w-grid and exponential table are needed (the already-certified
last-cell table). Cell data contain outward moment and Gaussian
intervals, per-bin endpoint bounds, and a compact symmetric-LDL
witness. No arithmetic assertion is assumed: every input and all
matrix/pivot comparisons are separate finite decidable checks.
-/

namespace W5

structure ThetaCompactReplayCellData where
  a : ℚ
  b : ℚ
  steps : ℕ
  M : ℕ → QInterval
  E : ℕ → QInterval
  W : ThetaIntervalMatrix
  lower : Fin 12 → Fin 9 → ℚ
  upper : Fin 12 → Fin 9 → ℚ

def thetaCompactReplayInputBox (scale : ℤ) (p : ℤ × ℤ) : QInterval :=
  thetaLastCellReplayBox scale p.1 p.2

/-- External data are finite integer tables. Out-of-range entries
are irrelevant to a successful check (only the specified finite
index sets are used). -/
def thetaCompactReplayDataFromArrays
    (a b : ℚ) (steps : ℕ)
    (M E : Array (ℤ × ℤ)) (W : Array (Array (ℤ × ℤ)))
    (lo hi : Array (Array ℤ)) : ThetaCompactReplayCellData where
  a := a
  b := b
  steps := steps
  M := fun k => thetaCompactReplayInputBox 100000000 M[k]!
  E := fun n => thetaCompactReplayInputBox 10000000000000000000000000000000000000000 E[n]!
  W := Matrix.of (fun i j => thetaCompactReplayInputBox 1000000 ((W[i.val]!)[j.val]!))
  lower := fun i k => (((lo[i.val]!)[k.val]! : ℤ):ℚ)/10000000000000000
  upper := fun i k => (((hi[i.val]!)[k.val]! : ℤ):ℚ)/10000000000000000

def thetaCompactReplayFirst (d : ThetaCompactReplayCellData) : ThetaIntervalMatrix :=
  fun i j => thetaAuditedOneTermMomentInterval
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox d.a d.b)
    (thetaGeneralCellCubicBinomialCoefficientBox d.a d.b i j)
    d.M 9

def thetaCompactReplaySource (d : ThetaCompactReplayCellData) : ThetaIntervalMatrix :=
  Matrix.of (fun i j => QInterval.add
    (thetaAuditedPrefixInterval 7
      (thetaLastCellTermBox (thetaCompactReplayFirst d) d.E d.a d.b i j))
    thetaBulkSevenTailBox)

def thetaCompactReplayUpperSource (d : ThetaCompactReplayCellData) : ThetaIntervalMatrix :=
  let S := thetaCompactReplaySource d
  thetaDirectCacheMatrix (Matrix.of (fun i j => if i ≤ j then S i j else QInterval.point 0))

def ThetaCompactReplayEligible (d : ThetaCompactReplayCellData) : Prop :=
  (0:ℚ) < d.a ∧ d.a ≤ d.b ∧ d.b ≤ (145:ℚ)/256 ∧
  ThetaBulkGaussianEligibility d.a d.b ∧
  thetaGammaAutoMomentCheck d.steps d.a thetaLastCellGrid = true ∧
  thetaGammaAutoMomentCheck d.steps d.b thetaLastCellGrid = true

instance (d : ThetaCompactReplayCellData) : Decidable (ThetaCompactReplayEligible d) := by
  unfold ThetaCompactReplayEligible
  infer_instance

def ThetaCompactReplayExpFits (d : ThetaCompactReplayCellData) : Prop :=
  let E := thetaLastCellCachedExp d.a d.b
  ∀ n : Fin 7, 2 ≤ n.val →
    (d.E n.val).lo ≤ (E n.val).lo ∧ (E n.val).hi ≤ (d.E n.val).hi

instance (d : ThetaCompactReplayCellData) : Decidable (ThetaCompactReplayExpFits d) := by
  unfold ThetaCompactReplayExpFits
  infer_instance

def ThetaCompactReplayBinFits (d : ThetaCompactReplayCellData) (i : Fin 12) : Prop :=
  let L := thetaLastCellBinStart i
  let U := thetaLastCellBinEnd i
  let BLo := thetaGammaMemoLowerNineBin thetaLastCellWExp d.steps (d.a^2) L U
  let BHi := thetaGammaMemoUpperNineBin thetaLastCellWExp d.steps (d.b^2) L U
  ∀ k : Fin 9, d.lower i k ≤ (BLo k).lo ∧ (BHi k).hi ≤ d.upper i k

instance (d : ThetaCompactReplayCellData) (i : Fin 12) :
    Decidable (ThetaCompactReplayBinFits d i) := by
  unfold ThetaCompactReplayBinFits
  infer_instance

-- The original recursive 12-bin grid sum is right associated.
def thetaCompactReplaySum12 (f : Fin 12 → ℚ) : ℚ :=
  f (0:Fin 12) + (f (1:Fin 12) + (f (2:Fin 12) + (f (3:Fin 12) + (f (4:Fin 12) + (f (5:Fin 12) + (f (6:Fin 12) + (f (7:Fin 12) + (f (8:Fin 12) + (f (9:Fin 12) + (f (10:Fin 12) + (f (11:Fin 12) + 0)))))))))))

def thetaCompactReplayGammaBox (d : ThetaCompactReplayCellData) (k : Fin 9) : QInterval :=
  ⟨thetaCompactReplaySum12 (fun i => d.lower i k),
    thetaCompactReplaySum12 (fun i => d.upper i k) +
      (thetaLastCellWExp 48).hi *
        (thetaGammaBinPolyQ k.val 48 +
          (d.b^2/4)*thetaGammaBinPolyQ (k.val+1) 48)⟩

def ThetaCompactReplayMomentSumsFit (d : ThetaCompactReplayCellData) : Prop :=
  ∀ k : Fin 9,
    (d.M k.val).lo ≤ (thetaCompactReplayGammaBox d k).lo ∧
    (thetaCompactReplayGammaBox d k).hi ≤ (d.M k.val).hi

instance (d : ThetaCompactReplayCellData) : Decidable (ThetaCompactReplayMomentSumsFit d) := by
  unfold ThetaCompactReplayMomentSumsFit
  infer_instance

def ThetaCompactReplayGammaFits (d : ThetaCompactReplayCellData) : Prop :=
  (∀ i : Fin 12, ThetaCompactReplayBinFits d i) ∧ ThetaCompactReplayMomentSumsFit d

instance (d : ThetaCompactReplayCellData) : Decidable (ThetaCompactReplayGammaFits d) := by
  unfold ThetaCompactReplayGammaFits
  infer_instance

def ThetaCompactReplayMatrixFits (d : ThetaCompactReplayCellData) : Prop :=
  ThetaUpperMatrixRefines d.W (thetaCompactReplayUpperSource d)

instance (d : ThetaCompactReplayCellData) : Decidable (ThetaCompactReplayMatrixFits d) := by
  unfold ThetaCompactReplayMatrixFits
  infer_instance

def ThetaCompactReplayArithmeticFits (d : ThetaCompactReplayCellData) : Prop :=
  ThetaCompactReplayEligible d ∧ ThetaCompactReplayExpFits d ∧
  ThetaCompactReplayMatrixFits d ∧ thetaDirectLDLCheck (thetaSymmetricIntervals d.W) = true

instance (d : ThetaCompactReplayCellData) : Decidable (ThetaCompactReplayArithmeticFits d) := by
  unfold ThetaCompactReplayArithmeticFits
  infer_instance

end W5
