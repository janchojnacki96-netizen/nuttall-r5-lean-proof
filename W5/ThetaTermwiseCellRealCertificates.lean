import W5.ThetaFiniteTermIntervalFold
import W5.ThetaAllCorrectionSummabilityFubini

/-!
# Reuse the already verified all-25 correction-summability theorem

PR #86 proved, using Mathlib and separable Gaussian majorants,
that EVERY true thetaCertificateCorrectionTerm series is summable
for 0 < x ≤ 1. We import that existing verified argument rather
than introduce a redundant proof or leave summability as a
hypothesis in the actual audited range x ≤ 145/256.

This module makes the genuine theta series prefix/tail split
UNCONDITIONAL in the relevant range, and reduces a cell's
analytic validation to termwise enclosures and a tail enclosure.

These finite-term and tail enclosures are still OPEN analytic
obligations, not consequences of the existing 255 rational
pivot tests. No numeric data are invented here.
-/

namespace W5

/-- All original theta series are summable in the complete
certificate domain, by reusing the preexisting Fubini proof. -/
theorem thetaAuditedSeriesTerm_summable_of_pos_le_one
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) :
    Summable (fun n : ℕ => thetaAuditedSeriesTerm x i j n) :=
  thetaAuditedSeriesTerm_summable x hx i j
    (thetaCertificateCorrectionTerm_all_summable x hx hx1 i j)

/-- No summability assumption is required any more. -/
theorem thetaCoefficient_eq_audited_prefix_add_tail_unconditional
    (N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) :
    thetaCoefficient x i j =
      thetaAuditedPrefix N x i j + thetaAuditedTail N x i j :=
  thetaCoefficient_eq_audited_prefix_add_tail N x hx i j
    (thetaCertificateCorrectionTerm_all_summable x hx hx1 i j)

/-- Soundness of termwise finite rational enclosures plus a
true remaining-series tail interval. The only hypotheses about
infinite series are the term/tail bounds themselves; convergence
is now a THEOREM from the earlier all-25 Gaussian-Fubini proof. -/
theorem thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    (N : ℕ) (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (J : ℕ → QInterval) (C T : QInterval)
    (hterm : ∀ n ∈ Finset.range N,
      QInterval.ContainsReal (J n) (thetaAuditedSeriesTerm x i j n))
    (htail : QInterval.ContainsReal T (thetaAuditedTail N x i j))
    (hlo : C.lo ≤
      (QInterval.add (thetaAuditedPrefixInterval N J) T).lo)
    (hhi : (QInterval.add
      (thetaAuditedPrefixInterval N J) T).hi ≤ C.hi) :
    QInterval.ContainsReal C (thetaCoefficient x i j) :=
  thetaCoefficient_containsReal_of_termwise_bounds_and_tail
    N x hx i j J C T
    (thetaCertificateCorrectionTerm_all_summable x hx hx1 i j)
    hterm htail hlo hhi

/-- Concrete cell certificate format for the original 768-bit data:
N is a per-cell finite cutoff; J holds exact rational intervals for
the finitely many genuine theta terms; T bounds the infinite tail.

The BOUND b≤1 is explicitly required to invoke the pre-existing
Gaussian-Fubini theorem, and holds for all audited cells. -/
def ThetaTermTailCellCertificate
    (a b : ℚ) (C : ThetaIntervalMatrix) : Prop :=
  ∃ N : ℕ, ∃ J : Matrix (Fin 5) (Fin 5) (ℕ → QInterval),
    ∃ T : ThetaIntervalMatrix,
      (b : ℝ) ≤ 1 ∧
      (∀ i j : Fin 5, i ≤ j →
        (C i j).lo ≤
          (QInterval.add
            (thetaAuditedPrefixInterval N (J i j)) (T i j)).lo ∧
        (QInterval.add
          (thetaAuditedPrefixInterval N (J i j)) (T i j)).hi ≤
            (C i j).hi) ∧
      ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
        ∀ i j : Fin 5, i ≤ j →
          (∀ n ∈ Finset.range N,
            QInterval.ContainsReal (J i j n)
              (thetaAuditedSeriesTerm x i j n)) ∧
          QInterval.ContainsReal (T i j) (thetaAuditedTail N x i j)

/-- Reuse the exact existing 15-entry upper-triangle real enclosure
target; no new matrix / LDL determinant algebra is needed. -/
theorem thetaUpperEnclosure_of_termwise_and_tail
    (a b : ℚ) (C : ThetaIntervalMatrix)
    (h : ThetaTermTailCellCertificate a b C) :
    ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (C i j) (thetaCoefficient x i j) := by
  rcases h with ⟨N, J, T, hb1, hinside, hbounds⟩
  intro x hx hax hxb i j hij
  have hx1 : x ≤ 1 := le_trans hxb hb1
  obtain ⟨hterm, htail⟩ := hbounds x hx hax hxb i j hij
  obtain ⟨hlo, hhi⟩ := hinside i j hij
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    N x hx hx1 i j (J i j) (C i j) (T i j)
    hterm htail hlo hhi

/-- A 51-cell chain of explicit termwise/tail certificates has no
hidden analytic summability assumptions. -/
def ThetaTermTailCertificateChain :
    ℚ → List ℚ → List ThetaIntervalMatrix → Prop
  | _, [], [] => True
  | a, b :: bs, C :: Cs =>
      ThetaTermTailCellCertificate a b C ∧
        ThetaTermTailCertificateChain b bs Cs
  | _, _, _ => False

/-- Every imported matrix's genuine-theta enclosure follows
from separately proved finite term / infinite tail intervals. -/
theorem thetaCellMatricesEnclose_of_term_tail :
    ∀ (a : ℚ) (bs : List ℚ) (Cs : List ThetaIntervalMatrix),
      ThetaTermTailCertificateChain a bs Cs →
        ThetaCellMatricesEnclose a bs Cs := by
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
          change ThetaTermTailCellCertificate a b C ∧
            ThetaTermTailCertificateChain b bs Cs at h
          rcases h with ⟨hfirst, hrest⟩
          change (∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
            ∀ i j : Fin 5, i ≤ j →
              QInterval.ContainsReal (C i j) (thetaCoefficient x i j)) ∧
            ThetaCellMatricesEnclose b bs Cs
          exact ⟨thetaUpperEnclosure_of_termwise_and_tail a b C hfirst,
            ih b Cs hrest⟩

/-- Finite LDL and all 25 original correction summability facts are
already proved. Real positivity now follows from the *still open*
51-cell termwise and tail interval enclosures. -/
theorem analyticMatrixPositive_of_audited_term_tail_certificates
    (h : ThetaTermTailCertificateChain
      0 endpoints thetaAuditUpperCellMatrices) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_audited_768bit_enclosures
    (thetaCellMatricesEnclose_of_term_tail
      0 endpoints thetaAuditUpperCellMatrices h)

end W5
