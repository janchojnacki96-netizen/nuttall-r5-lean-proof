import W5.ThetaGammaSharperFirstSquare
import W5.ThetaBulk48GeneratedVerifier

/-!
# ONE 48-cell original theta checker with sharp, CERTIFIED Gamma moments

The original generated checker failed the fifth LDL pivot in the
last x-cell. This module substitutes exactly ONE ingredient:
the n=1 matrix receives the new fully certified endpoint Gamma
moment enclosures, rather than the older cubic global bounds.

The n=2,...,6 signed Gaussian term generator, n>=7 infinite tail,
all 25 matrix entries and all five LDL pivots remain unchanged.
Only TWO executable rational Gamma checks per x-cell are added.

As in the original generator, a false Boolean means the enclosures
are not yet sharp enough. The final Boolean equality is intentionally
left as an explicit hypothesis until a true exact computation exists.
-/

namespace W5

/-- All original theta prefix terms, now with a genuinely certified
high-accuracy first-square moment matrix. -/
def thetaBulkSharpGammaTermBox
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else if n = 1 then
    thetaGammaSharperFirstSquareMatrix steps a b us i j
  else
    thetaBulkGeneratedSignedTerm a b i j n

/-- One finite original theta coefficient matrix and the original
globally certified n>=7 error. -/
def thetaBulkSharpGammaCellMatrix
    (steps : ℕ) (us : List ℚ) (a b : ℚ) :
    ThetaIntervalMatrix :=
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSharpGammaTermBox steps us a b i j))
      thetaBulkSevenTailBox)

/-- The generated matrix encloses the ACTUAL infinite theta entries.
This proof shares the old real-sound Gaussian and global-tail
lemmas; the new n=1 case uses the proved full Gamma moment grid. -/
theorem thetaBulkSharpGammaCellMatrix_containsReal
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaBulkSharpGammaCellMatrix steps us a b i j)
      (thetaCoefficient x i j) := by
  have haR : (0:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha.le
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal
        (thetaBulkSharpGammaTermBox steps us a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [thetaBulkSharpGammaTermBox,
        thetaAuditedSeriesTerm_zero,
        QInterval.ContainsReal, QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        simpa [thetaBulkSharpGammaTermBox] using
          (thetaGammaSharperFirstSquareMatrix_containsReal
            steps a b us x ha.le hx hax hxb hb1 hA hB i j)
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        simpa [thetaBulkSharpGammaTermBox, hn0, hn1] using
          (thetaBulkGeneratedSignedTerm_containsReal
            a b x ha hx hax hxb hb hExp i j n hn2 hn7)
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSharpGammaTermBox steps us a b i j))
      thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j
    (thetaBulkSharpGammaTermBox steps us a b i j)
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSharpGammaTermBox steps us a b i j))
      thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- A single finite rational Boolean checks all remaining theta cells
with the now-sharp, fully justified original n=1 moments. -/
def thetaBulk48SharpGammaCheck
    (steps : ℕ) (us : List ℚ) : ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
        ThetaBulkGaussianEligibility a b ∧
        thetaGammaAutoMomentCheck steps a us = true ∧
        thetaGammaAutoMomentCheck steps b us = true ∧
        intervalLDL5AlternatingCheck
          (thetaSymmetricIntervals
            (thetaBulkSharpGammaCellMatrix steps us a b)) = true) &&
      thetaBulk48SharpGammaCheck steps us b bs

/-- Uniform real-semantic soundness of one Boolean sweep; no
additional theorem per moment, per matrix entry, or per x-cell. -/
theorem thetaBulk48SharpGammaCheck_sound
    (steps : ℕ) (us : List ℚ) (bs : List ℚ) :
    ∀ (a : ℚ),
      thetaBulk48SharpGammaCheck steps us a bs = true →
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
            thetaGammaAutoMomentCheck steps a us = true ∧
            thetaGammaAutoMomentCheck steps b us = true ∧
            intervalLDL5AlternatingCheck
              (thetaSymmetricIntervals
                (thetaBulkSharpGammaCellMatrix steps us a b)) = true) ∧
            thetaBulk48SharpGammaCheck steps us b bs = true := by
        simpa only [thetaBulk48SharpGammaCheck,
          Bool.and_eq_true, decide_eq_true_eq] using hcheck
      rcases hs with ⟨⟨ha, hab, hb, hExp, hA, hB, hldl⟩, hrest⟩
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs
      refine ⟨?_, ih b hrest⟩
      refine ⟨thetaBulkSharpGammaCellMatrix steps us a b,
        intervalLDL5Alternating_of_check
          (thetaSymmetricIntervals
            (thetaBulkSharpGammaCellMatrix steps us a b))
          hldl, ?_⟩
      intro x hx hax hxb i j _
      have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
        have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
          exact_mod_cast hb
        simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
      exact thetaBulkSharpGammaCellMatrix_containsReal
        steps us a b x ha hx hax hxb hbR hExp hA hB i j

/-- Conditional full 48-cell original-theta result. The actual
finite Boolean computation is still open and MUST be verified
before invoking this theorem to assert R5 theta sign regularity. -/
theorem analyticMatrixPositive_of_bulk48_sharp_gamma
    (steps : ℕ) (us : List ℚ)
    (hcheck : thetaBulk48SharpGammaCheck steps us
      (821/2048:ℚ) (endpoints.drop 3) = true) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaBulk48SharpGammaCheck_sound
      steps us (endpoints.drop 3) (821/2048:ℚ) hcheck)

end W5
