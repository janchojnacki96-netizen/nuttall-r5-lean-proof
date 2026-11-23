import W5.ThetaThirdCellRemaining48Reduction
import W5.ThetaGlobalTailSeven
import W5.ThetaTermwiseCellRealCertificates
import W5.ThetaGenericCubicGammaCellCertificate

/-!
# ONE bulk verifier for all 48 remaining R5 theta x-cells

We no longer construct a separate theorem or PR for each x-cell.
The common original theta matrix is bounded by:

  * n=0: exactly ZERO;
  * n=1: the EXISTING genuine cubic-Gamma interval generator;
  * n=2,...,6: one uniform source of two-sided SIGNED intervals;
  * n>=7: the EXISTING proved real uniform tail <10^(-20).

The only missing input is a computable, real-sound *signed* interval
generator for the five intermediate terms. A single Bool traversal
then checks ALL 48 candidate matrices with the same verified
interval LDL5 checker, including rational domain endpoints.

Crucially the boolean check is not misrepresented as proof of the
transcendental bounds: a separate global original-term real
soundness theorem is required, and is made explicit in the API.
No numerical data are copied and no 48 manual proof cases appear.
-/

namespace W5

/-- A single executable generator for every original n=2,...,6
theta series term at every rational x-cell and every matrix entry.
The generator itself will be instantiated by a rational
interval evaluator; no trust in the generator is assumed. -/
abbrev ThetaBulkSignedTermGenerator :=
  ℚ → ℚ → Fin 5 → Fin 5 → ℕ → QInterval

/-- The genuinely missing ANALYTIC implication for one common
signed-rational interval generator. This must be proved once, for
arbitrary rational endpoints and each of the five finite indices.
It cannot be inferred merely from the finite LDL check. -/
def ThetaBulkSignedTermSound
    (J : ThetaBulkSignedTermGenerator) : Prop :=
  ∀ (a b : ℚ) (x : ℝ),
    (0:ℝ) ≤ (a:ℝ) → 0 < x →
    (a:ℝ) ≤ x → x ≤ (b:ℝ) →
    (b:ℝ) ≤ (145:ℝ)/256 →
    ∀ (i j : Fin 5) (n : ℕ), 2 ≤ n → n < 7 →
      QInterval.ContainsReal (J a b i j n)
        (thetaAuditedSeriesTerm x i j n)

/-- The ONE universal tail interval, with exact rational endpoints. -/
def thetaBulkSevenTailBox : QInterval :=
  ⟨-(1/(10:ℚ)^20), 1/(10:ℚ)^20⟩

/-- Genuine original theta-series tail enclosure, uniform across
ALL x-cells and all coefficient indices. No summability premise. -/
theorem thetaBulkSevenTailBox_containsReal
    (x : ℝ) (hx : 0 < x)
    (hxb : x ≤ (145:ℝ)/256) (i j : Fin 5) :
    QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) := by
  have h := (thetaGlobal_allEntriesTail_seven_abs_lt_oneE20
    x hx hxb i j).le
  simpa only [thetaBulkSevenTailBox, QInterval.ContainsReal,
    Rat.cast_neg, Rat.cast_div, Rat.cast_pow, Rat.cast_one,
    Rat.cast_ofNat] using (abs_le.mp h)

/-- The common 7-entry original theta series prefix enclosure;
n=1 reuses the certified cubic-Gamma generator, n=0 is zero,
and n=2,...,6 use exactly ONE signed term generator J. -/
def thetaBulkSevenTermBox
    (J : ThetaBulkSignedTermGenerator) (a b : ℚ)
    (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else if n = 1 then thetaGeneralCellCubicFirstSquareMatrix a b i j
  else J a b i j n

/-- The single executable rational interval matrix to check on
every one of the 48 remaining adjacent x-cells. -/
def thetaBulkSevenCellMatrix
    (J : ThetaBulkSignedTermGenerator) (a b : ℚ) :
    ThetaIntervalMatrix :=
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSevenTermBox J a b i j))
      thetaBulkSevenTailBox)

/-- One proof of REAL semantic soundness for all 25 matrix entries
of every generated cell. This is independent of LDL arithmetic:
one analytical theorem for J plus existing Mathlib integration
and the global n>=7 tail give all entrywise inclusions. -/
theorem thetaBulkSevenCellMatrix_containsReal
    (J : ThetaBulkSignedTermGenerator)
    (hJ : ThetaBulkSignedTermSound J)
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℝ) ≤ (a:ℝ)) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaBulkSevenCellMatrix J a b i j)
      (thetaCoefficient x i j) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal (thetaBulkSevenTermBox J a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [thetaBulkSevenTermBox, thetaAuditedSeriesTerm_zero,
        QInterval.ContainsReal, QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        simpa [thetaBulkSevenTermBox] using
          (thetaGeneralCellCubicFirstSquareMatrix_containsReal
            a b x ha hx hax hxb hb1 i j)
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        simpa [thetaBulkSevenTermBox, hn0, hn1] using
          (hJ a b x ha hx hax hxb hb i j n hn2 hn7)
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add (thetaAuditedPrefixInterval 7
       (thetaBulkSevenTermBox J a b i j)) thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j (thetaBulkSevenTermBox J a b i j)
    (QInterval.add (thetaAuditedPrefixInterval 7
      (thetaBulkSevenTermBox J a b i j)) thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- ONE Boolean sweep through every generated exact rational
matrix, simultaneously verifying its allowed x-range and all
five signed LDL pivots. A failure identifies an inadequate
interval generator, not a proof of Nuttall. -/
def thetaBulkSevenMatricesCheck
    (J : ThetaBulkSignedTermGenerator) : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      decide ((0:ℚ) ≤ a) &&
      decide (b ≤ (145:ℚ)/256) &&
      intervalLDL5AlternatingCheck
        (thetaSymmetricIntervals (thetaBulkSevenCellMatrix J a b)) &&
      thetaBulkSevenMatricesCheck J b bs

/-- No per-cell formalization is needed: induction proves once
that the ONE Boolean traversal plus the ONE analytic generator
soundness theorem imply all genuine theta x-cell certificates. -/
theorem thetaBulkSevenMatricesCheck_sound
    (J : ThetaBulkSignedTermGenerator)
    (hJ : ThetaBulkSignedTermSound J)
    (bs : List ℚ) :
    ∀ a : ℚ,
      thetaBulkSevenMatricesCheck J a bs = true →
      ThetaUpperRealCellCertificateChain a bs := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a hcheck
      have hsplit :
          ((0:ℚ) ≤ a ∧ b ≤ (145:ℚ)/256) ∧
          intervalLDL5AlternatingCheck
            (thetaSymmetricIntervals
              (thetaBulkSevenCellMatrix J a b)) = true ∧
          thetaBulkSevenMatricesCheck J b bs = true := by
        simpa only [thetaBulkSevenMatricesCheck,
          Bool.and_eq_true, decide_eq_true_eq] using hcheck
      rcases hsplit with ⟨⟨ha, hb⟩, hldl, hrest⟩
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs
      refine ⟨?_, ih b hrest⟩
      refine ⟨thetaBulkSevenCellMatrix J a b,
        intervalLDL5Alternating_of_check
          (thetaSymmetricIntervals (thetaBulkSevenCellMatrix J a b))
          hldl, ?_⟩
      intro x hx hax hxb i j _
      have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
      have hcast : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
        exact_mod_cast hb
      have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hcast
      exact thetaBulkSevenCellMatrix_containsReal
        J hJ a b x haR hx hax hxb hbR i j

/-- THE SINGLE remaining 48-cell numerical goal:
  thetaBulkSevenMatricesCheck J (821/2048) (endpoints.drop 3) = true.

No list of 48 separate lemmas is needed. To prove R5 theta signs
from it, separately prove the original n=2,...,6 real-soundness
of this SAME signed interval generator J. -/
theorem analyticMatrixPositive_of_bulk_48_seven_term_certificate
    (J : ThetaBulkSignedTermGenerator)
    (hJ : ThetaBulkSignedTermSound J)
    (hcheck : thetaBulkSevenMatricesCheck J
      (821/2048:ℚ) (endpoints.drop 3) = true) :
    analyticMatrixPositive := by
  exact analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaBulkSevenMatricesCheck_sound J hJ
      (endpoints.drop 3) (821/2048:ℚ) hcheck)

end W5
