import W5.ThetaEarlyRoundedBothCellMatrix

/-!
# Cheap short-circuit gate for the two restrictive theta entries

The verified 768-bit audited fifth pivot is most sensitive to
the entries (4,4) and (3,4) of the genuine real theta matrix.
Computing the full 15-entry early-rounded source can be expensive.
Reject any source whose two highest-impact intervals already
fail to fit the original audit BEFORE evaluating the remaining
coefficients. This preserves the exact original final checker.

A returned true Boolean still entails the REAL analytic
theta enclosures by direct reuse of the existing soundness lemma.
The gate cannot assert a previously failed audit as successful.
-/

namespace W5

/-- Every individual comparison remains on EXACT rationals.
An early false prevents evaluating the final all-15 checker. -/
def thetaEarlyRoundedPriorityAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  let source := thetaEarlyRoundedBothCellMatrix steps us K a b
  decide ((target 4 4).lo ≤ (source 4 4).lo ∧
    (source 4 4).hi ≤ (target 4 4).hi) &&
  decide ((target 3 4).lo ≤ (source 3 4).lo ∧
    (source 3 4).hi ≤ (target 3 4).hi) &&
  thetaEarlyRoundedBothCellAuditCheck steps us K target a b

/-- Proved transfer: true of the priority gate implies exactly
the old audited real-enclosure checker is true, with no weaker
numerical condition or unverified sign assumption. -/
theorem thetaEarlyRoundedPriorityAuditCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ)
    (hcheck : thetaEarlyRoundedPriorityAuditCheck
      steps us K target a b = true) :
    ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j)
          (thetaCoefficient x i j) := by
  have hmain :
      thetaEarlyRoundedBothCellAuditCheck
        steps us K target a b = true := by
    simp only [thetaEarlyRoundedPriorityAuditCheck,
      Bool.and_eq_true] at hcheck
    exact hcheck.2
  exact thetaEarlyRoundedBothCellAuditCheck_sound
    steps us K target a b hmain

end W5
