import W5.ThetaAudited51CellCertificateBridge
import W5.ThetaAllBaseCoefficientsSummability
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Split every original theta coefficient into a finite prefix and a tail

The independent 768-bit integer auditor computes finitely many square-index
terms and bounds the remaining infinite tail. This module makes that
partition precise INSIDE Lean for the genuine coefficient `thetaCoefficient`,
rather than replacing it with a Gaussian proxy.

The only analytic hypotheses are made explicit: summability of the true
integral correction series and sound real enclosures of the finite prefix
and the remaining tail. The underlying base series is already summable
by an existing Mathlib-based theorem; the infinite-series decomposition
is reused from `Summable.sum_add_tsum_nat_add`.

No rational numerical enclosures, exp/sqrt approximations, correction
summability, or tail estimates are asserted without proof.
-/

namespace W5

/-- The exact n-th contribution to the ORIGINAL theta coefficient,
including both the elementary base and weighted-integral correction. -/
noncomputable def thetaAuditedSeriesTerm
    (x : ℝ) (i j : Fin 5) (n : ℕ) : ℝ :=
  thetaCertificateBaseTerm x i j n -
    thetaCertificateCorrectionTerm x i j n

/-- The first N terms; n = 0 contributes zero in the original formula. -/
noncomputable def thetaAuditedPrefix
    (N : ℕ) (x : ℝ) (i j : Fin 5) : ℝ :=
  ∑ n ∈ Finset.range N, thetaAuditedSeriesTerm x i j n

/-- The exact, untruncated remaining infinite theta series. -/
noncomputable def thetaAuditedTail
    (N : ℕ) (x : ℝ) (i j : Fin 5) : ℝ :=
  ∑' n : ℕ, thetaAuditedSeriesTerm x i j (n + N)

/-- We do not assume elementary base summability: it is already
established for every coefficient by `thetaCertificateBaseTerm_all_summable`.
Only the genuine integral correction still needs a summability proof. -/
theorem thetaAuditedSeriesTerm_summable
    (x : ℝ) (hx : 0 < x) (i j : Fin 5)
    (hc : Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x i j n)) :
    Summable (fun n : ℕ => thetaAuditedSeriesTerm x i j n) := by
  exact (thetaCertificateBaseTerm_all_summable x hx i j).sub hc

/-- Exact equality between the original transcendental coefficient and
its finite prefix plus infinite tail; this is Mathlib's standard
summable-series partition, with no derivative/tsum interchange. -/
theorem thetaCoefficient_eq_audited_prefix_add_tail
    (N : ℕ) (x : ℝ) (hx : 0 < x) (i j : Fin 5)
    (hc : Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x i j n)) :
    thetaCoefficient x i j =
      thetaAuditedPrefix N x i j + thetaAuditedTail N x i j := by
  have hs := thetaAuditedSeriesTerm_summable x hx i j hc
  calc
    thetaCoefficient x i j =
        ∑' n : ℕ, thetaAuditedSeriesTerm x i j n :=
      thetaCoefficient_eq_tsum_base_sub_correction x i j
    _ = thetaAuditedPrefix N x i j + thetaAuditedTail N x i j :=
      (hs.sum_add_tsum_nat_add N).symm

/-- One rigorous real interval enclosure for a TRUE theta
coefficient can be obtained by adding independently bounded finite
prefix and infinite tail, then checking exact rational containment.
The last two inequalities are a finite exact-rational proof obligation. -/
theorem thetaCoefficient_containsReal_of_audited_prefix_tail
    (N : ℕ) (x : ℝ) (hx : 0 < x) (i j : Fin 5)
    (C P T : QInterval)
    (hc : Summable (fun n : ℕ =>
      thetaCertificateCorrectionTerm x i j n))
    (hp : QInterval.ContainsReal P (thetaAuditedPrefix N x i j))
    (ht : QInterval.ContainsReal T (thetaAuditedTail N x i j))
    (hlo : C.lo ≤ (QInterval.add P T).lo)
    (hhi : (QInterval.add P T).hi ≤ C.hi) :
    QInterval.ContainsReal C (thetaCoefficient x i j) := by
  have hadd := QInterval.add_containsReal hp ht
  rw [← thetaCoefficient_eq_audited_prefix_add_tail N x hx i j hc] at hadd
  have hlow : (C.lo : ℝ) ≤ ((QInterval.add P T).lo : ℝ) := by
    exact_mod_cast hlo
  have hhigh : ((QInterval.add P T).hi : ℝ) ≤ (C.hi : ℝ) := by
    exact_mod_cast hhi
  exact ⟨hlow.trans hadd.1, hadd.2.trans hhigh⟩

/-- One auditable real-theta cell now needs THREE independent witnesses:
a finite-term prefix interval P, an infinite-tail interval T, and
the exact rational inclusion P+T inside the already imported
768-bit candidate matrix C.

The cutoff N is per-cell, allowing the original integer auditor's
near/far split (N=12 or N=2). -/
def ThetaPrefixTailCellCertificate
    (a b : ℚ) (C : ThetaIntervalMatrix) : Prop :=
  ∃ N : ℕ, ∃ P T : ThetaIntervalMatrix,
    (∀ i j : Fin 5, i ≤ j →
      (C i j).lo ≤ (QInterval.add (P i j) (T i j)).lo ∧
      (QInterval.add (P i j) (T i j)).hi ≤ (C i j).hi) ∧
    ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        Summable (fun n : ℕ =>
          thetaCertificateCorrectionTerm x i j n) ∧
        QInterval.ContainsReal (P i j) (thetaAuditedPrefix N x i j) ∧
        QInterval.ContainsReal (T i j) (thetaAuditedTail N x i j)

/-- The prefix/tail witnesses imply the exact genuine-theta upper
triangle enclosure needed by the verified interval-LDL checker. -/
theorem thetaUpperEnclosure_of_prefix_tail
    (a b : ℚ) (C : ThetaIntervalMatrix)
    (hcell : ThetaPrefixTailCellCertificate a b C) :
    ∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (C i j) (thetaCoefficient x i j) := by
  rcases hcell with ⟨N, P, T, hinside, hreal⟩
  intro x hx ha hb i j hij
  obtain ⟨hc, hp, ht⟩ := hreal x hx ha hb i j hij
  obtain ⟨hlo, hhi⟩ := hinside i j hij
  exact thetaCoefficient_containsReal_of_audited_prefix_tail
    N x hx i j (C i j) (P i j) (T i j) hc hp ht hlo hhi

/-- Match a separate prefix/tail certificate to every cell in the
original ordered rational partition, with no silent dropped cells. -/
def ThetaPrefixTailCertificateChain :
    ℚ → List ℚ → List ThetaIntervalMatrix → Prop
  | _, [], [] => True
  | a, b :: bs, C :: Cs =>
      ThetaPrefixTailCellCertificate a b C ∧
        ThetaPrefixTailCertificateChain b bs Cs
  | _, _, _ => False

/-- All 51 analytic matrix enclosures follow from their independently
audited prefix/tail components. The existing LDL / Schur / determinant
soundness theorems are reused verbatim. -/
theorem thetaCellMatricesEnclose_of_prefix_tail :
    ∀ (a : ℚ) (bs : List ℚ) (Cs : List ThetaIntervalMatrix),
      ThetaPrefixTailCertificateChain a bs Cs →
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
          change ThetaPrefixTailCellCertificate a b C ∧
            ThetaPrefixTailCertificateChain b bs Cs at h
          rcases h with ⟨hfirst, hrest⟩
          change (∀ x : ℝ, 0 < x → (a : ℝ) ≤ x → x ≤ (b : ℝ) →
            ∀ i j : Fin 5, i ≤ j →
              QInterval.ContainsReal (C i j) (thetaCoefficient x i j)) ∧
            ThetaCellMatricesEnclose b bs Cs
          exact ⟨thetaUpperEnclosure_of_prefix_tail a b C hfirst,
            ih b Cs hrest⟩

/-- With all FINITE rational LDL checks from #123 already proved,
one can now complete the real-theta matrix signs by proving the
explicit prefix/tail certificate chain for the imported 51 cells.
This theorem does not claim such witnesses have yet been constructed. -/
theorem analyticMatrixPositive_of_audited_prefix_tail_certificates
    (hcert : ThetaPrefixTailCertificateChain
      0 endpoints thetaAuditUpperCellMatrices) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_audited_768bit_enclosures
    (thetaCellMatricesEnclose_of_prefix_tail
      0 endpoints thetaAuditUpperCellMatrices hcert)

end W5
