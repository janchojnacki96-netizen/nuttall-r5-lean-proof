import W5.ThetaRunningOriginalMatrix

/-!
# Single-pass priority gate for the original certified theta matrix

For each subcell, FIRST run the cheap exact-rational eligibility
predicates. Only then build the 5x5 original interval matrix ONCE,
check the restrictive A44 and A34 entries, and reuse that same matrix
for all remaining upper-entry inclusions. The former priority gate
also called the full cell checker, which re-created the source matrix.

The underlying real theta interval proof and original 255 audited
pivot signs are unchanged. All numerical inclusion checks remain
explicit: no assertion that the 48-cell Boolean is true is introduced.
-/

namespace W5

/-- Independent exact-rational preflight: no Gamma moments or
matrix coefficients are evaluated if this predicate fails. -/
def thetaRunningCellEligible
    (steps : ℕ) (us : List ℚ) (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b)

/-- The source matrix is shared by the fast A44/A34 checks and by
the complete 15 upper-entry matrix containment test. -/
def thetaRunningSinglePassAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  thetaRunningCellEligible steps us a b &&
    (let source := thetaRunningBothCellMatrix steps us K a b
     decide ((target 4 4).lo ≤ (source 4 4).lo ∧
       (source 4 4).hi ≤ (target 4 4).hi) &&
     (decide ((target 3 4).lo ≤ (source 3 4).lo ∧
       (source 3 4).hi ≤ (target 3 4).hi) &&
      thetaUpperMatrixRefinesCheck target source))

/-- The fast checker is stronger than the existing SOUND whole-cell
checker. The two priority tests are simply short-circuit guards,
not approximations or new assumptions. -/
theorem thetaRunningSinglePassAuditCheck_implies_original
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ)
    (h : thetaRunningSinglePassAuditCheck
      steps us K target a b = true) :
    thetaRunningBothCellAuditCheck steps us K target a b = true := by
  have hh : thetaRunningCellEligible steps us a b = true ∧
      thetaUpperMatrixRefinesCheck target
        (thetaRunningBothCellMatrix steps us K a b) = true := by
    simp only [thetaRunningSinglePassAuditCheck,
      Bool.and_eq_true] at h
    exact ⟨h.1, h.2.2.2⟩
  simpa only [thetaRunningBothCellAuditCheck,
    thetaRunningCellEligible, Bool.and_eq_true] using hh

/-- Inherits every REAL theta containment statement of the
unmodified old original-cell checker. -/
theorem thetaRunningSinglePassAuditCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ)
    (h : thetaRunningSinglePassAuditCheck
      steps us K target a b = true) :
    ∀ x : ℝ, 0 < x → (a:ℝ) ≤ x → x ≤ (b:ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j) (thetaCoefficient x i j) := by
  exact thetaRunningBothCellAuditCheck_sound
    steps us K target a b
    (thetaRunningSinglePassAuditCheck_implies_original
      steps us K target a b h)

/-- The original audited interval data are tested with identical
semantics but without computing failing subcell matrices twice. -/
def thetaRunningSinglePass48Check
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ)) : Bool :=
  thetaGenericAuditedSubgridsCheck
    (thetaRunningSinglePassAuditCheck steps us K)
    (821/2048 : ℚ) (endpoints.drop 3)
    (thetaAuditUpperCellMatrices.drop 3) grids

/-- Conditional exact certificate for all 48 remaining genuine
theta cells: still requires evaluating the finite Boolean to true. -/
theorem analyticMatrixPositive_of_single_pass48
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ))
    (h : thetaRunningSinglePass48Check steps us K grids = true) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_audited_enclosures
  exact thetaGenericAuditedSubgridsCheck_sound
    (thetaRunningSinglePassAuditCheck steps us K)
    (fun target a b =>
      thetaRunningSinglePassAuditCheck_sound steps us K target a b)
    (endpoints.drop 3) (821/2048 : ℚ)
    (thetaAuditUpperCellMatrices.drop 3) grids h

end W5
