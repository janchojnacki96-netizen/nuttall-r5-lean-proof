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
          exact_mod_cast hfar
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

end W5
