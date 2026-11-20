import W5.VerifiedIntervalDivision
import W5.FiniteCore

/-!
# A reusable, proved five-step signed LDL interval propagation engine

The existing W5 certificate has 51 rational x-intervals and five LDL
pivot signs per interval. Instead of individually certifying all 255
arithmetic update steps, build ONE generic verified rational matrix
checker, whose soundness is proved by induction on the elimination
step count.

The proof reuses W5.QInterval.schurUpdate_contains, already checked
in PR #91, without reproving reciprocal monotonicity or signed
four-corner multiplication. The exact rational matrix undergoes
precisely the same Schur updates as the enclosing interval matrix.

Provided each calculated pivot interval excludes zero, every
intermediate matrix encloses the corresponding exact elimination
matrix. Furthermore, alternating checker output signs produce
the same strict signs for all five exact pivots.

The next separate task is to supply rigorously enclosed real
theta-coefficient matrices on each of the 51 x-subintervals,
and to connect these exact rational pivots to the real determinant
using Matrix Schur complement identities. This module alone does
not certify the analytic theta coefficients or their signs.
-/

namespace W5

/-- Every entry of a rational matrix is enclosed by its
corresponding exact rational interval. -/
def MatrixIntervalContains {n : Type*} (B : Matrix n n QInterval)
    (A : Matrix n n ℚ) : Prop :=
  ∀ i j : n, QInterval.Contains (B i j) (A i j)

/-- The exact rational matrix Schur pivot update, with
division interpreted in the rational field. -/
noncomputable def exactSchurStep {n : Type*}
    (A : Matrix n n ℚ) (k : n) : Matrix n n ℚ :=
  Matrix.of (fun i j => A i j - A i k * A k j / A k k)

/-- The interval Schur pivot update. It is computable using
exact rational endpoints and never relies on floating point. -/
def intervalSchurStep {n : Type*}
    (B : Matrix n n QInterval) (k : n) : Matrix n n QInterval :=
  Matrix.of (fun i j => QInterval.schurUpdate
    (B i j) (B i k) (B k j) (B k k))

/-- One matrix Schur elimination step preserves enclosure,
assuming its pivot interval is strictly signed. -/
theorem intervalSchurStep_contains {n : Type*}
    {A : Matrix n n ℚ} {B : Matrix n n QInterval}
    (h : MatrixIntervalContains B A) (k : n)
    (hsgn : 0 < (B k k).lo ∨ (B k k).hi < 0) :
    MatrixIntervalContains (intervalSchurStep B k)
      (exactSchurStep A k) := by
  intro i j
  simpa [intervalSchurStep, exactSchurStep, Matrix.of_apply]
    using QInterval.schurUpdate_contains
      (h i j) (h i k) (h k j) (h k k) hsgn

/-- The pivot chosen at step k. For the first five steps,
its index is literally k; mod 5 only totalizes the definition. -/
def pivotIndexFive (k : ℕ) : Fin 5 :=
  ⟨k % 5, Nat.mod_lt k (by omega)⟩

/-- Repeated exact Schur elimination, selecting pivots 0..4.
No nonsingularity assumption is required to define field division,
but the soundness checker below only accepts signed pivots. -/
noncomputable def exactLDL5 (A : Matrix (Fin 5) (Fin 5) ℚ) :
    ℕ → Matrix (Fin 5) (Fin 5) ℚ
  | 0 => A
  | k + 1 => exactSchurStep (exactLDL5 A k) (pivotIndexFive k)

/-- The analogous algorithm on certified rational intervals. -/
def intervalLDL5 (B : Matrix (Fin 5) (Fin 5) QInterval) :
    ℕ → Matrix (Fin 5) (Fin 5) QInterval
  | 0 => B
  | k + 1 => intervalSchurStep (intervalLDL5 B k) (pivotIndexFive k)

/-- A single reusable sign hypothesis on the five intermediate
pivot interval enclosures. Each is checked by rational comparisons. -/
def intervalLDL5PivotsSeparated
    (B : Matrix (Fin 5) (Fin 5) QInterval) : Prop :=
  ∀ k : ℕ, k < 5 →
    0 < ((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).lo ∨
    ((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).hi < 0

/-- Inductively propagate correct containment through all
five elimination steps, given a single initial matrix enclosure
and five strictly signed pivot interval checks. -/
theorem intervalLDL5_contains_exact
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hstart : MatrixIntervalContains B A)
    (hsep : intervalLDL5PivotsSeparated B)
    (m : ℕ) (hm : m ≤ 5) :
    MatrixIntervalContains (intervalLDL5 B m) (exactLDL5 A m) := by
  induction m with
  | zero =>
      simpa only [intervalLDL5, exactLDL5] using hstart
  | succ k ih =>
      have hk : k < 5 := by omega
      have hprev := ih (by omega : k ≤ 5)
      change MatrixIntervalContains
        (intervalSchurStep (intervalLDL5 B k) (pivotIndexFive k))
        (exactSchurStep (exactLDL5 A k) (pivotIndexFive k))
      exact intervalSchurStep_contains hprev
        (pivotIndexFive k) (hsep k hk)

/-- A strict lower endpoint of an interval pivot proves a
strictly positive actual pivot; similarly for a strict upper
endpoint proving negativity. No numerical sign is guessed. -/
theorem intervalLDL5_pivot_sign_sound
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hstart : MatrixIntervalContains B A)
    (hsep : intervalLDL5PivotsSeparated B)
    (k : ℕ) (hk : k < 5) :
    (0 < ((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).lo →
       0 < ((exactLDL5 A k) (pivotIndexFive k) (pivotIndexFive k))) ∧
    (((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).hi < 0 →
       ((exactLDL5 A k) (pivotIndexFive k) (pivotIndexFive k)) < 0) := by
  have h := intervalLDL5_contains_exact A B hstart hsep k (by omega)
    (pivotIndexFive k) (pivotIndexFive k)
  exact ⟨fun hpos => lt_of_lt_of_le hpos h.1,
    fun hneg => lt_of_le_of_lt h.2 hneg⟩

/-- A deterministic five-pivot SIGN PATTERN (positive at even
steps, negative at odd steps). The checker itself is exact
rational arithmetic; no transcendental evaluation is used. -/
def intervalLDL5Alternating
    (B : Matrix (Fin 5) (Fin 5) QInterval) : Prop :=
  ∀ k : ℕ, k < 5 →
    if k % 2 = 0 then
      0 < ((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).lo
    else
      ((intervalLDL5 B k) (pivotIndexFive k) (pivotIndexFive k)).hi < 0

/-- Passing the five alternating finite interval tests
entails the exact five strict rational pivot signs. This
one theorem can be reused on all 51 certified x-intervals. -/
theorem intervalLDL5Alternating_sound
    (A : Matrix (Fin 5) (Fin 5) ℚ)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hstart : MatrixIntervalContains B A)
    (hchecks : intervalLDL5Alternating B)
    (k : ℕ) (hk : k < 5) :
    if k % 2 = 0 then
      0 < ((exactLDL5 A k) (pivotIndexFive k) (pivotIndexFive k))
    else
      ((exactLDL5 A k) (pivotIndexFive k) (pivotIndexFive k)) < 0 := by
  have hsep : intervalLDL5PivotsSeparated B := by
    intro i hi
    have hcheck := hchecks i hi
    by_cases hp : i % 2 = 0
    · exact Or.inl (by simpa only [if_pos hp] using hcheck)
    · exact Or.inr (by simpa only [if_neg hp] using hcheck)
  have hsign := intervalLDL5_pivot_sign_sound A B hstart hsep k hk
  have hcheck := hchecks k hk
  by_cases hp : k % 2 = 0
  · simpa only [if_pos hp] using hsign.1 (by simpa only [if_pos hp] using hcheck)
  · simpa only [if_neg hp] using hsign.2 (by simpa only [if_neg hp] using hcheck)

end W5
