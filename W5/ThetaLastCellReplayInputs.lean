import W5.ThetaLastCellCompactDyadicBase

/-!
# Small rational input witnesses for the last-cell computation

All nine moment intervals are rounded *outward* to 10^-8 and the five
Gaussian factors to 10^-40. The expensive source generator is used only
to validate the small input witnesses, never inside a matrix entry.
No witness is assumed sound: independent checks and the existing real
containment lemmas are required before concluding a cell certificate.
-/

namespace W5

def thetaLastCellReplayBox (scale l u : ℤ) : QInterval :=
  ⟨(l:ℚ)/(scale:ℚ), (u:ℚ)/(scale:ℚ)⟩

def thetaLastCellReplayMomentWitness (k : ℕ) : QInterval :=
  match k with
  | 0 => thetaLastCellReplayBox 100000000 106292581 106924491
  | 1 => thetaLastCellReplayBox 100000000 111415898 113093390
  | 2 => thetaLastCellReplayBox 100000000 231996711 237001798
  | 3 => thetaLastCellReplayBox 100000000 722436107 738822807
  | 4 => thetaLastCellReplayBox 100000000 2992363423 3051401370
  | 5 => thetaLastCellReplayBox 100000000 15446608373 15687409347
  | 6 => thetaLastCellReplayBox 100000000 95360451436 96528640763
  | 7 => thetaLastCellReplayBox 100000000 684661795424 691712060870
  | 8 => thetaLastCellReplayBox 100000000 5603010311709 5656181399770
  | _ => QInterval.point 0

def thetaLastCellReplayExpWitness (n : ℕ) : QInterval :=
  let D : ℤ := 10000000000000000000000000000000000000000
  match n with
  | 2 => thetaLastCellReplayBox D 856361581676900456071074653999604461 868651719751134096409342925280180131
  | 3 => thetaLastCellReplayBox D 142479528191773632716167833916 147997764964921100560972190823
  | 4 => thetaLastCellReplayBox D 46055964121058502322 49457074016213946966
  | 5 => thetaLastCellReplayBox D 28923936 32416452
  | 6 => thetaLastCellReplayBox D 0 1
  | _ => QInterval.point 0

def thetaLastCellReplayGammaDegree (g j : Fin 3) : Fin 9 :=
  ⟨3*g.val+j.val, by omega⟩

/-- Evaluate only three of the nine moments in each numerical job,
sharing the original Gamma-grid closure within the group. -/
def thetaLastCellReplayGammaGroupSource (g : Fin 3) : Fin 3 → QInterval :=
  let S := thetaGammaRunningCellNine 8 thetaLastCellA thetaLastCellB 1 thetaLastCellGrid
  let cached : Array QInterval := Array.ofFn (fun j : Fin 3 =>
    S (thetaLastCellReplayGammaDegree g j))
  fun j => cached[j.val]'(by simpa [cached] using j.isLt)

theorem thetaLastCellReplayGammaGroupSource_apply (g j : Fin 3) :
    thetaLastCellReplayGammaGroupSource g j =
      thetaGammaRunningCellNine 8 thetaLastCellA thetaLastCellB 1 thetaLastCellGrid
        (thetaLastCellReplayGammaDegree g j) := by
  simp [thetaLastCellReplayGammaGroupSource]

def ThetaLastCellReplayGammaGroupFits (g : Fin 3) : Prop :=
  ∀ j : Fin 3,
    (thetaLastCellReplayMomentWitness (thetaLastCellReplayGammaDegree g j).val).lo ≤
      (thetaLastCellReplayGammaGroupSource g j).lo ∧
    (thetaLastCellReplayGammaGroupSource g j).hi ≤
      (thetaLastCellReplayMomentWitness (thetaLastCellReplayGammaDegree g j).val).hi

instance (g : Fin 3) : Decidable (ThetaLastCellReplayGammaGroupFits g) := by
  unfold ThetaLastCellReplayGammaGroupFits
  infer_instance

/-- Compare only the five true Gaussian input intervals. -/
def ThetaLastCellReplayExpFits : Prop :=
  let E := thetaLastCellCachedExp thetaLastCellA thetaLastCellB
  ∀ n : Fin 7, 2 ≤ n.val →
    (thetaLastCellReplayExpWitness n.val).lo ≤ (E n.val).lo ∧
    (E n.val).hi ≤ (thetaLastCellReplayExpWitness n.val).hi

instance : Decidable ThetaLastCellReplayExpFits := by
  unfold ThetaLastCellReplayExpFits
  infer_instance

def thetaLastCellReplayFirst : ThetaIntervalMatrix :=
  fun i j => thetaAuditedOneTermMomentInterval
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox thetaLastCellA thetaLastCellB)
    (thetaGeneralCellCubicBinomialCoefficientBox thetaLastCellA thetaLastCellB i j)
    thetaLastCellReplayMomentWitness 9

/-- No root bisection or exponential Taylor evaluation is performed
inside this matrix: all transcendental inputs are compact witnesses. -/
def thetaLastCellReplaySource : ThetaIntervalMatrix :=
  Matrix.of (fun i j => QInterval.add
    (thetaAuditedPrefixInterval 7
      (thetaLastCellTermBox thetaLastCellReplayFirst thetaLastCellReplayExpWitness
        thetaLastCellA thetaLastCellB i j))
    thetaBulkSevenTailBox)

/-- Compute only the upper-triangular entries of one row. -/
def thetaLastCellReplayRowSource (i : Fin 5) : Fin 5 → QInterval :=
  thetaDirectCacheFive (fun j => if i ≤ j then thetaLastCellReplaySource i j
    else QInterval.point 0)

theorem thetaLastCellReplayRowSource_apply (i j : Fin 5) (hij : i ≤ j) :
    thetaLastCellReplayRowSource i j = thetaLastCellReplaySource i j := by
  simp [thetaLastCellReplayRowSource, thetaDirectCacheFive_apply, hij]

def ThetaLastCellReplayRowFits (i : Fin 5) : Prop :=
  ∀ j : Fin 5, i ≤ j →
    (thetaLastCellWitness i j).lo ≤ (thetaLastCellReplayRowSource i j).lo ∧
    (thetaLastCellReplayRowSource i j).hi ≤ (thetaLastCellWitness i j).hi

instance (i : Fin 5) : Decidable (ThetaLastCellReplayRowFits i) := by
  unfold ThetaLastCellReplayRowFits
  infer_instance

end W5
