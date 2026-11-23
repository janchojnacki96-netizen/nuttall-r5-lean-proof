import W5.ThetaBulkFixedExponential
import W5.ThetaBulkSignedIntervalEvaluator

/-!
# One complete, reusable Boolean audit of ALL 48 remaining theta cells

This module COMPOSES the independent verified analytic building blocks:
* exact signed (not absolute-value) original theta factorial coefficients;
* genuine Gamma moment interval bounds on every rational x-cell;
* Gaussian exponential using 65-term Taylor + 768-bit squaring;
* global original theta n>=7 analytic tail < 10^-20;
* the existing five signed LDL pivot checker.

One single Boolean checker tests every cell's parameter eligibility,
all five Gaussian exponential ranges n=2..6, and five matrix pivots.
One Lean induction proves the checker sound for ALL 48 cells.

Important: the final Boolean equality is a goal, NOT an axiom or a
claimed success. The computed intervals might be too wide to pass
the LDL test even if the original theorem is true. The checker
reports such failure rather than hiding it.
-/

namespace W5

/-- A real-sound, computable, signed original n-th term candidate
for ALL 25 theta matrix entries, generated from only [a,b] and n.
No per-cell hand-coded tables or numerical oracle. -/
def thetaBulkGeneratedSignedTerm : ThetaBulkSignedTermGenerator :=
  fun a b i j n =>
    thetaBulkSignedOriginalTermBox a b n i j
      (thetaBulkFixedGaussianExpBox a b n)

/-- All positive original Gaussian factors n=2,...,6 are certified
by one rational predicate over Fin 7, so this can be checked by
the native finite-rational evaluator without trust in floating point. -/
def ThetaBulkGaussianEligibility (a b : ℚ) : Prop :=
  ∀ n : Fin 7, 2 ≤ n.val →
    (thetaBulkReducedExpArgBox a b n.val).hi ≤ (1:ℚ)/3 ∧
    0 < (thetaBulkExpTaylorBox
      (thetaBulkReducedExpArgBox a b n.val)).lo

/-- Constructive finite decision procedure for the seven-index Gaussian
eligibility condition; no classical oracle or untrusted numerical data. -/
instance thetaBulkGaussianEligibility_decidable (a b : ℚ) :
    Decidable (ThetaBulkGaussianEligibility a b) :=
  Fintype.decidableForallFintype

/-- A general real-enclosure lemma for the original n-th signed
term. Only the rational Gaussian eligibility is required. -/
theorem thetaBulkGeneratedSignedTerm_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a)
    (hx : 0 < x) (hax : (a:ℝ) ≤ x)
    (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (i j : Fin 5) (n : ℕ) (hn2 : 2 ≤ n)
    (hn7 : n < 7) :
    QInterval.ContainsReal
      (thetaBulkGeneratedSignedTerm a b i j n)
      (thetaAuditedSeriesTerm x i j n) := by
  have hx1 : (b:ℝ) ≤ 1 := by linarith
  have hEl := hExp ⟨n,hn7⟩ hn2
  have hE :
      QInterval.ContainsReal
        (thetaBulkFixedGaussianExpBox a b n)
        (Real.exp (-((n:ℝ)^2-1)/x^2)) :=
    thetaBulkFixedGaussianExpBox_containsReal
      a b x n ha hax hxb hn2 hEl.1 hEl.2
  exact thetaBulkSignedOriginalTermBox_containsReal
    a b x ha hx hax hxb hx1 i j n (by omega)
    (thetaBulkFixedGaussianExpBox a b n) hE

/-- The exact generated 7-term matrix encloses the ORIGINAL,
infinite theta coefficient series, without assuming the old 768-bit
Python audit entries. n=0 is zero, n=1 uses certified cubic Gamma,
n=2..6 use the signed finite evaluator, n>=7 uses the global tail. -/
theorem thetaBulkGeneratedCellMatrix_containsReal
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a)
    (hx : 0 < x) (hax : (a:ℝ) ≤ x)
    (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaBulkSevenCellMatrix thetaBulkGeneratedSignedTerm a b i j)
      (thetaCoefficient x i j) := by
  have haR : (0:ℝ) ≤ (a:ℝ) := by
    exact_mod_cast ha.le
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal
        (thetaBulkSevenTermBox thetaBulkGeneratedSignedTerm a b i j n)
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
            a b x haR hx hax hxb hb1 i j)
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        simpa [thetaBulkSevenTermBox, hn0, hn1] using
          thetaBulkGeneratedSignedTerm_containsReal
            a b x ha hx hax hxb hb hExp i j n hn2 hn7
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSevenTermBox thetaBulkGeneratedSignedTerm a b i j))
      thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j
    (thetaBulkSevenTermBox thetaBulkGeneratedSignedTerm a b i j)
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSevenTermBox thetaBulkGeneratedSignedTerm a b i j))
      thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- A single executable checker of ALL remaining x-cells.
Each step checks exact rational bounds for a,b and n=2..6,
then EXACTLY the existing original five-pivot LDL5 Boolean test.
A false result exposes insufficient interval sharpness. -/
def thetaBulk48GeneratedCheck : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      decide ((0:ℚ) < a ∧ a ≤ b ∧
        b ≤ (145:ℚ)/256 ∧
        ThetaBulkGaussianEligibility a b ∧
        intervalLDL5AlternatingCheck
          (thetaSymmetricIntervals
            (thetaBulkSevenCellMatrix
              thetaBulkGeneratedSignedTerm a b)) = true) &&
      thetaBulk48GeneratedCheck b bs

/-- ONE uniform soundness theorem for the bulk Boolean verifier.
Unlike finite LDL data alone, this proves its output is a certificate
for the TRUE transcendental theta entries on every rational x-cell. -/
theorem thetaBulk48GeneratedCheck_sound (bs : List ℚ) :
    ∀ (a : ℚ),
      thetaBulk48GeneratedCheck a bs = true →
      ThetaUpperRealCellCertificateChain a bs := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a hcheck
      have hs :
          ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
            ThetaBulkGaussianEligibility a b ∧
            intervalLDL5AlternatingCheck
              (thetaSymmetricIntervals
                (thetaBulkSevenCellMatrix
                  thetaBulkGeneratedSignedTerm a b)) = true) ∧
            thetaBulk48GeneratedCheck b bs = true := by
        simpa only [thetaBulk48GeneratedCheck,
          Bool.and_eq_true, decide_eq_true_eq] using hcheck
      rcases hs with ⟨⟨ha, hab, hb, hExp, hldl⟩, hrest⟩
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs
      refine ⟨?_, ih b hrest⟩
      refine ⟨thetaBulkSevenCellMatrix thetaBulkGeneratedSignedTerm a b,
        intervalLDL5Alternating_of_check
          (thetaSymmetricIntervals
            (thetaBulkSevenCellMatrix thetaBulkGeneratedSignedTerm a b))
          hldl, ?_⟩
      intro x hx hax hxb i j _
      have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
        have h : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
          exact_mod_cast hb
        simpa only [Rat.cast_div, Rat.cast_ofNat] using h
      exact thetaBulkGeneratedCellMatrix_containsReal
        a b x ha hx hax hxb hbR hExp i j

/-- ONE final finite computation would now establish all REAL
theta five-pivot signs on the original x-range.
There are no unproved real inequalities in this implication;
only the explicit, decidable rational Boolean value remains. -/
theorem analyticMatrixPositive_of_bulk_48_generated_check
    (hcheck : thetaBulk48GeneratedCheck
      (821/2048:ℚ) (endpoints.drop 3) = true) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaBulk48GeneratedCheck_sound
      (endpoints.drop 3) (821/2048:ℚ) hcheck)

/-!
Intentionally NO native_decide assertion of the last Boolean.
We need to TEST how many cells' generated numerical intervals are
sharp enough before asserting that the entire value is true.
The original imported 768-bit Boolean pivot certificate remains
valid independently, but is NOT silently substituted for
the analytic containment of these generated matrices.
-/

end W5
