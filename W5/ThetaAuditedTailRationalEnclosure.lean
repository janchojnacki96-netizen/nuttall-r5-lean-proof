import W5.ThetaAuditedOriginalFullTail
import W5.ThetaTermwiseCellRealCertificates

/-!
# Exact rational enclosures for the TRUE original theta infinite tails

Reuse the proved near/far 10^(-35) bounds for the actual infinite
base-minus-integral-correction theta series (not a proxy series).
The single rational interval below supplies the formerly ASSUMED
tail-enclosure field in the existing PR #128 termwise certificate.

The only remaining nontrivial cell inputs are finitely many uniform
real enclosures of the genuine original series summands and exact
rational endpoint inclusion in the 768-bit candidate matrix.

No rational LDL computation, convergence proof, or analytic Gaussian
tail argument is repeated here.
-/

namespace W5

/-- An EXACT, closed rational interval with endpoints ±10^(-35).
Its real semantics are those already proved for QInterval. -/
def thetaAuditedTailErrorInterval : QInterval :=
  ⟨-(1 / (10 : ℚ)^35), 1 / (10 : ℚ)^35⟩

/-- Translate a strict absolute error estimate to the existing
rational-to-real interval semantics. -/
theorem thetaAuditedTailErrorInterval_containsReal_of_abs_lt
    (t : ℝ) (ht : |t| < 1 / (10 : ℝ)^35) :
    QInterval.ContainsReal thetaAuditedTailErrorInterval t := by
  have h : -(1 / (10 : ℝ)^35) ≤ t ∧
      t ≤ 1 / (10 : ℝ)^35 := abs_le.mp ht.le
  simpa only [QInterval.ContainsReal, thetaAuditedTailErrorInterval,
    Rat.cast_neg, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_one] using h

/-- The original infinite tail after the first twelve square
indices belongs to the EXACT rational error interval throughout
the whole near-auditor domain. -/
theorem thetaAuditedNearTail_rational_enclosure
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (145 : ℝ)/256)
    (i j : Fin 5) :
    QInterval.ContainsReal thetaAuditedTailErrorInterval
      (thetaAuditedTail 12 x i j) :=
  thetaAuditedTailErrorInterval_containsReal_of_abs_lt _
    (thetaAuditedNearTail_abs_lt_oneE35 x hx hxB i j)

/-- For x≤1/8 only the first two square indices are needed:
the true remaining infinite tail has the same rational enclosure. -/
theorem thetaAuditedFarTail_rational_enclosure
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) :
    QInterval.ContainsReal thetaAuditedTailErrorInterval
      (thetaAuditedTail 2 x i j) :=
  thetaAuditedTailErrorInterval_containsReal_of_abs_lt _
    (thetaAuditedFarTail_abs_lt_oneE35 x hx hxB i j)

/-- Deterministic per-cell cutoff. The smaller far cells use N=2;
all other cells use N=12. This is computable over exact rationals. -/
def thetaAuditedCellCutoff (b : ℚ) : ℕ :=
  if b ≤ (1 : ℚ)/8 then 2 else 12

/-- In contrast to the older term+tail cell certificate, this
requires ONLY finite original-term real interval enclosures and
rational containment. The tail is the fixed certified interval.
The rational upper-endpoint bound is explicit and decidable. -/
def ThetaAuditedFiniteCellCertificate
    (a b : ℚ) (C : ThetaIntervalMatrix) : Prop :=
  ∃ J : Matrix (Fin 5) (Fin 5) (ℕ → QInterval),
    (b : ℝ) ≤ (145 : ℝ)/256 ∧
    (∀ i j : Fin 5, i ≤ j →
      (C i j).lo ≤
        (QInterval.add
          (thetaAuditedPrefixInterval (thetaAuditedCellCutoff b) (J i j))
          thetaAuditedTailErrorInterval).lo ∧
      (QInterval.add
        (thetaAuditedPrefixInterval (thetaAuditedCellCutoff b) (J i j))
        thetaAuditedTailErrorInterval).hi ≤ (C i j).hi) ∧
    ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        ∀ n ∈ Finset.range (thetaAuditedCellCutoff b),
          QInterval.ContainsReal (J i j n)
            (thetaAuditedSeriesTerm x i j n)

/-- Discharge BOTH earlier analytic convergence and infinite-tail
enclosure requirements by reusing existing proved theorems. -/
theorem thetaAuditedFiniteCell_to_term_tail
    (a b : ℚ) (C : ThetaIntervalMatrix)
    (h : ThetaAuditedFiniteCellCertificate a b C) :
    ThetaTermTailCellCertificate a b C := by
  rcases h with ⟨J, hb, hinside, hterms⟩
  refine ⟨thetaAuditedCellCutoff b, J,
    (fun _ _ => thetaAuditedTailErrorInterval), ?_, ?_, ?_⟩
  · linarith
  · exact hinside
  · intro x hx hax hxb i j hij
    constructor
    · exact hterms x hx hax hxb i j hij
    · by_cases hfar : b ≤ (1 : ℚ)/8
      · have hbfar : (b : ℝ) ≤ (1 : ℝ)/8 := by
          have hmul : b * 8 ≤ (1 : ℚ) := by linarith [hfar]
          have hmulR : (b : ℝ) * 8 ≤ 1 := by exact_mod_cast hmul
          linarith
        simpa only [thetaAuditedCellCutoff, if_pos hfar] using
          (thetaAuditedFarTail_rational_enclosure x hx
            (hxb.trans hbfar) i j)
      · simpa only [thetaAuditedCellCutoff, if_neg hfar] using
          (thetaAuditedNearTail_rational_enclosure x hx
            (hxb.trans hb) i j)

/-- Reuse the EXISTING PR #128 chain checker instead of writing
another 51-cell interval or LDL checker. -/
def ThetaAuditedFiniteCertificateChain :
    ℚ → List ℚ → List ThetaIntervalMatrix → Prop
  | _, [], [] => True
  | a, b :: bs, C :: Cs =>
      ThetaAuditedFiniteCellCertificate a b C ∧
        ThetaAuditedFiniteCertificateChain b bs Cs
  | _, _, _ => False

theorem thetaAuditedFiniteCertificateChain_to_term_tail :
    ∀ (a : ℚ) (bs : List ℚ) (Cs : List ThetaIntervalMatrix),
      ThetaAuditedFiniteCertificateChain a bs Cs →
        ThetaTermTailCertificateChain a bs Cs := by
  intro a bs
  induction bs generalizing a with
  | nil =>
      intro Cs h
      cases Cs with
      | nil => trivial
      | cons C Cs => exact False.elim h
  | cons b bs ih =>
      intro Cs h
      cases Cs with
      | nil => exact False.elim h
      | cons C Cs =>
          change ThetaAuditedFiniteCellCertificate a b C ∧
            ThetaAuditedFiniteCertificateChain b bs Cs at h
          rcases h with ⟨hfirst, hrest⟩
          change ThetaTermTailCellCertificate a b C ∧
            ThetaTermTailCertificateChain b bs Cs
          exact ⟨thetaAuditedFiniteCell_to_term_tail a b C hfirst,
            ih b Cs hrest⟩

/-- All 255 certified rational LDL signs plus REAL full-theta
infinite-tail enclosures now reduce matrix positivity to ONLY
finite-term uniform interval proofs in the 51 audited cells. -/
theorem analyticMatrixPositive_of_audited_finite_term_certificates
    (h : ThetaAuditedFiniteCertificateChain
      0 endpoints thetaAuditUpperCellMatrices) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_audited_term_tail_certificates
    (thetaAuditedFiniteCertificateChain_to_term_tail
      0 endpoints thetaAuditUpperCellMatrices h)


/-!
## First far cell: eliminate the vacuous index zero

The first cell of the integer auditor, [0,1/8], retains only the n=1
contribution before the already rigorously bounded N=2 tail. We reuse
the proven correction summability and real interval-addition semantics
without duplicating any polynomial or numerical evaluation.
-/

/-- The artificial n=0 square-index contribution is literally zero,
including its genuine Lebesgue integral correction. -/
theorem thetaAuditedSeriesTerm_zero
    (x : ℝ) (i j : Fin 5) :
    thetaAuditedSeriesTerm x i j 0 = 0 := by
  simp [thetaAuditedSeriesTerm, thetaCertificateBaseTerm,
    thetaCertificateCorrectionTerm]

/-- The N=2 finite prefix used on the far cell consists of exactly
one nonzero original term. This is a definitional identity, not a
numerical approximation. -/
theorem thetaAuditedPrefix_two_eq_one
    (x : ℝ) (i j : Fin 5) :
    thetaAuditedPrefix 2 x i j =
      thetaAuditedSeriesTerm x i j 1 := by
  simp [thetaAuditedPrefix, Finset.sum_range_succ,
    thetaAuditedSeriesTerm_zero]

/-- For x in the first audited cell, the TRUE full theta coefficient
is exactly its n=1 contribution plus the proven tiny n≥2 tail.
The previous all-25 Mathlib Fubini summability theorem discharges
convergence with no additional hypothesis. -/
theorem thetaCoefficient_far_eq_one_add_tail
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) :
    thetaCoefficient x i j =
      thetaAuditedSeriesTerm x i j 1 +
        thetaAuditedTail 2 x i j := by
  have hx1 : x ≤ 1 := by linarith
  rw [thetaCoefficient_eq_audited_prefix_add_tail_unconditional
    2 x hx hx1 i j]
  rw [thetaAuditedPrefix_two_eq_one]

/-- Fully rigorous first-cell interval composition: ONLY the true
n=1 term needs a numerical real enclosure. The infinite tail,
its 10^(-35) rational interval, and convergence are all proved.
The last two rational comparisons can be checked by exact arithmetic
once a concrete first-term interval is supplied. -/
theorem thetaCoefficient_far_containsReal_of_one_term
    (x : ℝ) (hx : 0 < x) (hxB : x ≤ (1 : ℝ)/8)
    (i j : Fin 5) (I C : QInterval)
    (hfirst : QInterval.ContainsReal I
      (thetaAuditedSeriesTerm x i j 1))
    (hlo : C.lo ≤ (QInterval.add I thetaAuditedTailErrorInterval).lo)
    (hhi : (QInterval.add I thetaAuditedTailErrorInterval).hi ≤ C.hi) :
    QInterval.ContainsReal C (thetaCoefficient x i j) := by
  have hsum : QInterval.ContainsReal
      (QInterval.add I thetaAuditedTailErrorInterval)
      (thetaAuditedSeriesTerm x i j 1 +
        thetaAuditedTail 2 x i j) :=
    QInterval.add_containsReal hfirst
      (thetaAuditedFarTail_rational_enclosure x hx hxB i j)
  rw [← thetaCoefficient_far_eq_one_add_tail x hx hxB i j] at hsum
  have hlow : (C.lo : ℝ) ≤
      ((QInterval.add I thetaAuditedTailErrorInterval).lo : ℝ) := by
    exact_mod_cast hlo
  have hhigh :
      ((QInterval.add I thetaAuditedTailErrorInterval).hi : ℝ) ≤
        (C.hi : ℝ) := by
    exact_mod_cast hhi
  exact ⟨hlow.trans hsum.1, hsum.2.trans hhigh⟩

/-- First-cell uniform upper-triangle soundness can now be certified
with just fifteen real interval enclosures of the genuine n=1 term.
All n≥2 terms are covered unconditionally by the audited tail proof. -/
theorem thetaFirstFarCell_upperEnclosure_of_one_term
    (C J : ThetaIntervalMatrix)
    (hinside : ∀ i j : Fin 5, i ≤ j →
      (C i j).lo ≤
        (QInterval.add (J i j) thetaAuditedTailErrorInterval).lo ∧
      (QInterval.add (J i j) thetaAuditedTailErrorInterval).hi ≤
        (C i j).hi)
    (hterm : ∀ x : ℝ, 0 < x → x ≤ (1 : ℝ)/8 →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (J i j)
          (thetaAuditedSeriesTerm x i j 1)) :
    ∀ x : ℝ, 0 < x → x ≤ (1 : ℝ)/8 →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (C i j) (thetaCoefficient x i j) := by
  intro x hx hxB i j hij
  obtain ⟨hlo, hhi⟩ := hinside i j hij
  exact thetaCoefficient_far_containsReal_of_one_term
    x hx hxB i j (J i j) (C i j)
    (hterm x hx hxB i j hij) hlo hhi

end W5
