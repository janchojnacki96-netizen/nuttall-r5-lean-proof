import W5.ThetaSymmetric15EntryCellCertificates

/-!
# Decidable finite five-pivot interval checker for the original theta certificate

The existing `intervalLDL5Alternating` is stated as
`∀ k : ℕ, k < 5 → ...`, an infinite-domain proposition that is
unsuitable for direct computational checking with `decide`.

Replace it by an equivalent proposition over `Fin 5`. Lean/Mathlib
already provides executable decidable instances for:
* finite universal quantification over `Fin 5`;
* exact inequalities of rational numbers;
* the existing intervalLDL5 Schur arithmetic.

Thus `intervalLDL5AlternatingCheck` is a concrete Boolean checker
for any explicitly provided rational 5×5 interval matrix.
Its mathematical soundness reuses the EXISTING interval soundness
theorem; no new floating-point, proof oracle, or numerical assertion
is introduced.

Numerical endpoint matrices and rigorous theta enclosures must
still be imported separately. This module just removes a
computability obstacle in formalizing the certificate's 255 tests.
-/

namespace W5

/-- Finite (computationally decidable) equivalent of the existing
five signed LDL pivot inequalities. -/
def intervalLDL5AlternatingFin
    (B : Matrix (Fin 5) (Fin 5) QInterval) : Prop :=
  ∀ k : Fin 5,
    if k.val % 2 = 0 then
      0 < ((intervalLDL5 B k.val)
        (pivotIndexFive k.val) (pivotIndexFive k.val)).lo
    else
      ((intervalLDL5 B k.val)
        (pivotIndexFive k.val) (pivotIndexFive k.val)).hi < 0

/-- Exact logical equivalence with the already verified checker.
No algebraic calculations are repeated. -/
theorem intervalLDL5Alternating_iff_fin
    (B : Matrix (Fin 5) (Fin 5) QInterval) :
    intervalLDL5Alternating B ↔ intervalLDL5AlternatingFin B := by
  constructor
  · intro h k
    exact h k.val k.isLt
  · intro h k hk
    exact h ⟨k, hk⟩

/-- An executable Boolean checker consisting of the five *actual*
exact-rational pivot comparisons. Unlike a proposition-level
`decide (∀ k : Fin 5, ...)`, this directly uses the constructive
rational inequality decision procedure at each concrete pivot.
There is no classical noncomputable decision oracle. -/
def intervalLDL5AlternatingCheck
    (B : Matrix (Fin 5) (Fin 5) QInterval) : Bool :=
  decide (0 < ((intervalLDL5 B 0)
    (pivotIndexFive 0) (pivotIndexFive 0)).lo) &&
  decide (((intervalLDL5 B 1)
    (pivotIndexFive 1) (pivotIndexFive 1)).hi < 0) &&
  decide (0 < ((intervalLDL5 B 2)
    (pivotIndexFive 2) (pivotIndexFive 2)).lo) &&
  decide (((intervalLDL5 B 3)
    (pivotIndexFive 3) (pivotIndexFive 3)).hi < 0) &&
  decide (0 < ((intervalLDL5 B 4)
    (pivotIndexFive 4) (pivotIndexFive 4)).lo)

/-- Soundness of the executable five-stage Boolean test follows by
case analysis over the five possible indices, reducing each Boolean
comparison to a rational inequality. -/
theorem intervalLDL5Alternating_of_check
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (h : intervalLDL5AlternatingCheck B = true) :
    intervalLDL5Alternating B := by
  have hsigns :
      (0 < ((intervalLDL5 B 0)
        (pivotIndexFive 0) (pivotIndexFive 0)).lo) ∧
      (((intervalLDL5 B 1)
        (pivotIndexFive 1) (pivotIndexFive 1)).hi < 0) ∧
      (0 < ((intervalLDL5 B 2)
        (pivotIndexFive 2) (pivotIndexFive 2)).lo) ∧
      (((intervalLDL5 B 3)
        (pivotIndexFive 3) (pivotIndexFive 3)).hi < 0) ∧
      (0 < ((intervalLDL5 B 4)
        (pivotIndexFive 4) (pivotIndexFive 4)).lo) := by
    simpa only [intervalLDL5AlternatingCheck,
      Bool.and_eq_true, decide_eq_true_eq] using h
  rcases hsigns with ⟨h0, h1, h2, h3, h4⟩
  apply (intervalLDL5Alternating_iff_fin B).2
  intro k
  fin_cases k
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3
  · simpa using h4

/-- The 15-entry upper-triangle cell certificate can now be supplied
using ONE concrete Boolean result of the finite verified checker.
Only the true analytic entry enclosures remain hypotheses. -/
theorem thetaUpperRealCellCertificate_of_checked
    (a b : ℚ)
    (C : Matrix (Fin 5) (Fin 5) QInterval)
    (hcheck :
      intervalLDL5AlternatingCheck
        (thetaSymmetricIntervals C) = true)
    (hupper : ∀ x : ℝ, 0 < x →
      (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          QInterval.ContainsReal (C i j) (thetaCoefficient x i j)) :
    ThetaUpperRealCellCertificate a b :=
  ⟨C, intervalLDL5Alternating_of_check
    (thetaSymmetricIntervals C) hcheck, hupper⟩

end W5
