import W5.VerifiedIntervalLDL5
import W5.VerifiedIntervalRealSemantics
import W5.AnalyticTargets

/-!
# Real 5x5 LDL soundness from exact rational interval arithmetic

PR #92 has already kernel-verified the five-step LDL interval algorithm
on rational matrices, and PR #94 verified that identical rational
endpoints bound every arithmetic operation on real scalars.

This module COMPOSES those verified results:
* the exact real-valued Schur update is enclosed by the old rational
  interval update, with no new interval-arithmetic sign-case proof;
* containment is preserved across all five successive pivots;
* when the five rational interval pivots have pattern +,-,+,-,+,
  every pivot of the REAL matrix has the same strict sign;
* the original thetaCoefficient matrix is a direct instance.

No numerical theta enclosures are postulated: they remain visible as
an explicit premise supplied by a future transcendental certificate.
No determinant identity is assumed or asserted in this module.
-/

namespace W5

/-- Entrywise enclosure of a real matrix by rational intervals. -/
def MatrixIntervalContainsReal {n : Type*}
    (B : Matrix n n QInterval) (A : Matrix n n ℝ) : Prop :=
  ∀ i j : n, QInterval.ContainsReal (B i j) (A i j)

/-- An actual real Schur update, with real division. -/
noncomputable def realSchurStep {n : Type*}
    (A : Matrix n n ℝ) (k : n) : Matrix n n ℝ :=
  Matrix.of (fun i j => A i j - A i k * A k j / A k k)

/-- One verified interval Schur update encloses the true REAL
Schur update. The proof is exactly the already checked scalar
lemma from PR #94, lifted through Matrix.of. -/
theorem intervalSchurStep_containsReal {n : Type*}
    {A : Matrix n n ℝ} {B : Matrix n n QInterval}
    (h : MatrixIntervalContainsReal B A) (k : n)
    (hsgn : 0 < (B k k).lo ∨ (B k k).hi < 0) :
    MatrixIntervalContainsReal (intervalSchurStep B k)
      (realSchurStep A k) := by
  intro i j
  simpa [intervalSchurStep, realSchurStep, Matrix.of_apply]
    using QInterval.schurUpdate_containsReal
      (h i j) (h i k) (h k j) (h k k) hsgn

/-- Five successive real Schur updates (0 through 4).
This is the exact real counterpart to the already checked
intervalLDL5 algorithm; arithmetic stays over real numbers. -/
noncomputable def realLDL5 (A : Matrix (Fin 5) (Fin 5) ℝ) :
    ℕ → Matrix (Fin 5) (Fin 5) ℝ
  | 0 => A
  | k + 1 => realSchurStep (realLDL5 A k) (pivotIndexFive k)

/-- One induction, reused from PR #92, transports every one
of the five matrix enclosures from rational to REAL semantics.
The only additional assumption is the exact enclosure of the
initial real matrix. -/
theorem intervalLDL5_contains_real
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hstart : MatrixIntervalContainsReal B A)
    (hsep : intervalLDL5PivotsSeparated B)
    (m : ℕ) (hm : m ≤ 5) :
    MatrixIntervalContainsReal (intervalLDL5 B m) (realLDL5 A m) := by
  induction m with
  | zero =>
      simpa only [intervalLDL5, realLDL5] using hstart
  | succ k ih =>
      have hk : k < 5 := by omega
      have hprev := ih (by omega : k ≤ 5)
      change MatrixIntervalContainsReal
        (intervalSchurStep (intervalLDL5 B k) (pivotIndexFive k))
        (realSchurStep (realLDL5 A k) (pivotIndexFive k))
      exact intervalSchurStep_containsReal hprev
        (pivotIndexFive k) (hsep k hk)

/-- Every strict interval-pivot sign is sound for the
corresponding actual real pivot. -/
theorem intervalLDL5_pivot_sign_sound_real
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hstart : MatrixIntervalContainsReal B A)
    (hsep : intervalLDL5PivotsSeparated B)
    (k : ℕ) (hk : k < 5) :
    (0 < ((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).lo →
       0 < ((realLDL5 A k) (pivotIndexFive k) (pivotIndexFive k))) ∧
    (((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).hi < 0 →
       ((realLDL5 A k) (pivotIndexFive k) (pivotIndexFive k)) < 0) := by
  have h := intervalLDL5_contains_real A B hstart hsep k (by omega)
    (pivotIndexFive k) (pivotIndexFive k)
  constructor
  · intro hp
    have hr : (0:ℝ) <
        (((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).lo:ℝ) := by
      exact_mod_cast hp
    exact lt_of_lt_of_le hr h.1
  · intro hn
    have hr :
        (((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).hi:ℝ) < 0 := by
      exact_mod_cast hn
    exact lt_of_le_of_lt h.2 hr

/-- The one rational checker, already proved correct in PR #92,
also certifies the exact alternating five-pivot signs of ANY
real matrix enclosed by the input intervals. -/
theorem intervalLDL5Alternating_sound_real
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hstart : MatrixIntervalContainsReal B A)
    (hchecks : intervalLDL5Alternating B)
    (k : ℕ) (hk : k < 5) :
    if k % 2 = 0 then
      0 < ((realLDL5 A k) (pivotIndexFive k) (pivotIndexFive k))
    else
      ((realLDL5 A k) (pivotIndexFive k) (pivotIndexFive k)) < 0 := by
  have hsep : intervalLDL5PivotsSeparated B := by
    intro i hi
    have hcheck := hchecks i hi
    by_cases hp : i % 2 = 0
    · exact Or.inl (by simpa only [if_pos hp] using hcheck)
    · exact Or.inr (by simpa only [if_neg hp] using hcheck)
  have hsign :=
    intervalLDL5_pivot_sign_sound_real A B hstart hsep k hk
  have hcheck := hchecks k hk
  by_cases hp : k % 2 = 0
  · simpa only [if_pos hp] using hsign.1
      (by simpa only [if_pos hp] using hcheck)
  · simpa only [if_neg hp] using hsign.2
      (by simpa only [if_neg hp] using hcheck)

/-- The actual 5x5 original numerical theta certificate, with
no surrogate and no assumptions on its coefficients. -/
noncomputable def originalThetaMatrixFive (x : ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (fun i j : Fin 5 => thetaCoefficient x i j)

/-- DIRECT use with the original theta matrix.
The two remaining analytic/computational obligations are
precisely the true enclosure hentry and the finite signed
interval pivot checks hchecks. Both are visible. -/
theorem thetaCertificateFive_real_pivot_signs_of_interval
    (x : ℝ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j) (thetaCoefficient x i j))
    (hchecks : intervalLDL5Alternating B)
    (k : ℕ) (hk : k < 5) :
    if k % 2 = 0 then
      0 < ((realLDL5 (originalThetaMatrixFive x) k)
        (pivotIndexFive k) (pivotIndexFive k))
    else
      ((realLDL5 (originalThetaMatrixFive x) k)
        (pivotIndexFive k) (pivotIndexFive k)) < 0 := by
  have hstart : MatrixIntervalContainsReal B (originalThetaMatrixFive x) := by
    intro i j
    exact hentry i j
  exact intervalLDL5Alternating_sound_real
    (originalThetaMatrixFive x) B hstart hchecks k hk

end W5
