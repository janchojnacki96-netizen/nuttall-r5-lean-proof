import W5.ThetaBulkDegreeSelectedGammaCells

/-!
# Audit-scale compression of the certified selected-moment theta matrix

The signed Gamma-grid polynomial expressions can have very large
rational denominators. Before the five LDL Schur steps, round each
already-certified rational interval OUTWARD to the existing fixed
2^768 integer scale. This reduces operand sizes without altering
the true original theta coefficient or the analytic proof.

This is NOT an unproved numerical approximation: the already checked
thetaBulkRoundToAuditScale_containsReal is applied to every entry.

The same generic matrix checker applies to all n,k selections, all
25 coefficients and any finite partition. A false result stays false;
nothing assumes any pivot sign.
-/

namespace W5

/-- Every certificate entry is compressed to the existing 768-bit
integer denominator, with rigorous outward floor/ceiling. -/
def thetaBulkRoundedQInterval (I : QInterval) : QInterval :=
  (thetaBulkRoundToAuditScale I).asQInterval thetaAuditScale

theorem thetaBulkRoundedQInterval_containsReal
    (I : QInterval) (x : ℝ)
    (hI : QInterval.ContainsReal I x) :
    QInterval.ContainsReal (thetaBulkRoundedQInterval I) x := by
  exact thetaBulkRoundToAuditScale_containsReal I x hI

/-- The true 5-by-5 matrix using independently selected moment
degrees and square indices, with uniformly bounded denominators
before interval LDL elimination. -/
def thetaBulkRoundedDegreeSelectedCellMatrix
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  Matrix.of (fun i j =>
    thetaBulkRoundedQInterval
      (thetaBulkDegreeSelectedCellMatrix steps us K S a b i j))

/-- One generic REAL containment proof for every original theta
coefficient; no new integral, exponential, root or polynomial proof. -/
theorem thetaBulkRoundedDegreeSelectedCellMatrix_containsReal
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (hSel : ThetaBulkSelectedGammaEligibility steps us S a b)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaBulkRoundedDegreeSelectedCellMatrix steps us K S a b i j)
      (thetaCoefficient x i j) := by
  change QInterval.ContainsReal
    (thetaBulkRoundedQInterval
      (thetaBulkDegreeSelectedCellMatrix steps us K S a b i j))
    (thetaCoefficient x i j)
  exact thetaBulkRoundedQInterval_containsReal _
    (thetaCoefficient x i j)
    (thetaBulkDegreeSelectedCellMatrix_containsReal
      steps us K S a b x ha hx hax hxb hb hExp hA hB hSel i j)

/-- An executable exact-rational check for the rounded
5-by-5 matrix: all numerical hypotheses and five LDL signs. -/
def thetaBulkRoundedDegreeSelectedCellCheck
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility steps us S a b ∧
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals
        (thetaBulkRoundedDegreeSelectedCellMatrix steps us K S a b)) = true)

/-- Successful finite arithmetic implies genuine original
theta real-matrix pivot signs on the whole x-cell. -/
theorem thetaBulkRoundedDegreeSelectedCellCheck_sound
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ)
    (hcheck : thetaBulkRoundedDegreeSelectedCellCheck
      steps us K S a b = true) :
    ThetaUpperRealCellCertificate a b := by
  have h : (0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
      ThetaBulkGaussianEligibility a b ∧
      thetaGammaAutoMomentCheck steps a us = true ∧
      thetaGammaAutoMomentCheck steps b us = true ∧
      ThetaBulkSelectedGammaEligibility steps us S a b ∧
      intervalLDL5AlternatingCheck
        (thetaSymmetricIntervals
          (thetaBulkRoundedDegreeSelectedCellMatrix steps us K S a b)) = true :=
    of_decide_eq_true hcheck
  rcases h with ⟨ha, _, hb, hExp, hA, hB, hSel, hldl⟩
  refine ⟨thetaBulkRoundedDegreeSelectedCellMatrix steps us K S a b,
    intervalLDL5Alternating_of_check
      (thetaSymmetricIntervals
        (thetaBulkRoundedDegreeSelectedCellMatrix steps us K S a b)) hldl, ?_⟩
  intro x hx hax hxb i j _
  have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
      exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact thetaBulkRoundedDegreeSelectedCellMatrix_containsReal
    steps us K S a b x ha hx hax hxb hbR
    hExp hA hB hSel i j

/-- One generic, terminating Boolean pass over any x-grid.
No repeated proof per cell is necessary. -/
def thetaBulkRoundedDegreeSelectedCellsCheck
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ) :
    ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      thetaBulkRoundedDegreeSelectedCellCheck steps us K S a b &&
      thetaBulkRoundedDegreeSelectedCellsCheck steps us K S b bs

theorem thetaBulkRoundedDegreeSelectedCellsCheck_sound
    (steps : ℕ) (us : List ℚ)
    (K S : Finset ℕ) (bs : List ℚ) :
    ∀ a : ℚ,
      thetaBulkRoundedDegreeSelectedCellsCheck steps us K S a bs = true →
      ThetaUpperRealCellCertificateChain a bs := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a hcheck
      have hs :
          thetaBulkRoundedDegreeSelectedCellCheck steps us K S a b = true ∧
          thetaBulkRoundedDegreeSelectedCellsCheck steps us K S b bs = true := by
        simpa only [thetaBulkRoundedDegreeSelectedCellsCheck,
          Bool.and_eq_true] using hcheck
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs
      exact ⟨thetaBulkRoundedDegreeSelectedCellCheck_sound
        steps us K S a b hs.1, ih b hs.2⟩

/-- Conditional global analytic sign consequence. The finite
Boolean is a real obligation and has NOT been asserted true. -/
theorem analyticMatrixPositive_of_bulk48_rounded_selected_gamma
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (hcheck : thetaBulkRoundedDegreeSelectedCellsCheck steps us K S
      (821/2048:ℚ) (endpoints.drop 3) = true) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaBulkRoundedDegreeSelectedCellsCheck_sound
      steps us K S (endpoints.drop 3) (821/2048:ℚ) hcheck)

end W5
