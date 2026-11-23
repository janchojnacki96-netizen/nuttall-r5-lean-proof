import W5.ThetaBulkParameterizedGammaTerm
import W5.ThetaBulk48SharpGammaChecker

/-!
# One selectable high-precision Gamma evaluator for ALL original theta cells

The previously certified first-square moment is always used at n=1.
A finite set S determines which of n=2,...,6 also receive the
new exact finite-grid/infinite-tail moment intervals. The unselected
indices retain the existing signed cubic-Gamma enclosures.

The SAME analytic soundness proof and the SAME five-pivot LDL routine
work at every square index and every cell. One may check S={} first,
then S={2}, {2,3}, ... to identify the actual source of pivot inflation.
All choices are exact-rational and no result of a failed Boolean check
is promoted to a theorem.
-/

namespace W5

/-- Selectively sharpen an original theta summand at any n in S.
The first-square is always sharp; n=0 stays exactly zero. -/
def thetaBulkSelectedGammaTermBox
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else if n = 1 then thetaGammaSharperFirstSquareMatrix steps a b us i j
  else if n ∈ S then
    thetaBulkSharpHigherSquareTermBox steps us a b i j n
  else thetaBulkGeneratedSignedTerm a b i j n

/-- Exactly TWO endpoint moment checks for each selected n.
This is entirely rational and decidable, uniformly over all Fin 7. -/
def ThetaBulkSelectedGammaEligibility
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (a b : ℚ) : Prop :=
  ∀ n : Fin 7, 2 ≤ n.val → n.val ∈ S →
    thetaGammaAutoMomentCheck steps (a/(n.val:ℚ)) us = true ∧
    thetaGammaAutoMomentCheck steps (b/(n.val:ℚ)) us = true

instance thetaBulkSelectedGammaEligibility_decidable
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (a b : ℚ) :
    Decidable (ThetaBulkSelectedGammaEligibility steps us S a b) :=
  Fintype.decidableForallFintype

/-- The genuine theta coefficient interval using only selected
sharp moments; all other signed Gaussian terms and n>=7 tail are kept. -/
def thetaBulkSelectedGammaCellMatrix
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSelectedGammaTermBox steps us S a b i j))
      thetaBulkSevenTailBox)

/-- A SINGLE soundness theorem for all 25 theta coefficients, all
selectable subsets of n=2..6, and every rational cell [a,b]. -/
theorem thetaBulkSelectedGammaCellMatrix_containsReal
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
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
      (thetaBulkSelectedGammaCellMatrix steps us S a b i j)
      (thetaCoefficient x i j) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal
        (thetaBulkSelectedGammaTermBox steps us S a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [thetaBulkSelectedGammaTermBox,
        thetaAuditedSeriesTerm_zero,
        QInterval.ContainsReal, QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        simpa [thetaBulkSelectedGammaTermBox, hn0] using
          (thetaGammaSharperFirstSquareMatrix_containsReal
            steps a b us x ha.le hx hax hxb hb1 hA hB i j)
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        by_cases hns : n ∈ S
        · have hs := hSel ⟨n,hn7⟩ hn2 hns
          simpa [thetaBulkSelectedGammaTermBox, hn0, hn1, hns] using
            (thetaBulkSharpHigherSquareTermBox_containsReal
              steps us a b x ha hx hax hxb hb hExp i j n
              hn2 hn7 hs.1 hs.2)
        · simpa [thetaBulkSelectedGammaTermBox, hn0, hn1, hns] using
            (thetaBulkGeneratedSignedTerm_containsReal
              a b x ha hx hax hxb hb hExp i j n hn2 hn7)
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSelectedGammaTermBox steps us S a b i j))
      thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j
    (thetaBulkSelectedGammaTermBox steps us S a b i j)
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkSelectedGammaTermBox steps us S a b i j))
      thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- One-cell exact-rational Boolean check, including all required
moment and exponential eligibility conditions and five LDL pivots. -/
def thetaBulkSelectedGammaCellCheck
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility steps us S a b ∧
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals
        (thetaBulkSelectedGammaCellMatrix steps us S a b)) = true)

/-- Passing the executable Boolean gives REAL matrix sign
regularity on the actual cell, not just a numerical LDL computation. -/
theorem thetaBulkSelectedGammaCellCheck_sound
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (a b : ℚ)
    (hcheck : thetaBulkSelectedGammaCellCheck steps us S a b = true) :
    ThetaUpperRealCellCertificate a b := by
  have h : (0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
      ThetaBulkGaussianEligibility a b ∧
      thetaGammaAutoMomentCheck steps a us = true ∧
      thetaGammaAutoMomentCheck steps b us = true ∧
      ThetaBulkSelectedGammaEligibility steps us S a b ∧
      intervalLDL5AlternatingCheck
        (thetaSymmetricIntervals
          (thetaBulkSelectedGammaCellMatrix steps us S a b)) = true :=
    of_decide_eq_true hcheck
  rcases h with ⟨ha, _, hb, hExp, hA, hB, hSel, hldl⟩
  refine ⟨thetaBulkSelectedGammaCellMatrix steps us S a b,
    intervalLDL5Alternating_of_check
      (thetaSymmetricIntervals
        (thetaBulkSelectedGammaCellMatrix steps us S a b)) hldl, ?_⟩
  intro x hx hax hxb i j _
  have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
      exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact thetaBulkSelectedGammaCellMatrix_containsReal
    steps us S a b x ha hx hax hxb hbR
    hExp hA hB hSel i j

/-- One rational traversal across any number of theta cells;
set S to whichever n=2..6 moment degrees merit refinement. -/
def thetaBulkSelectedGammaCellsCheck
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ) :
    ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      thetaBulkSelectedGammaCellCheck steps us S a b &&
      thetaBulkSelectedGammaCellsCheck steps us S b bs

/-- One induction proves the uniform soundness of EVERY selected
sharp-moment cell and the complete exact-rational Boolean chain. -/
theorem thetaBulkSelectedGammaCellsCheck_sound
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ) (bs : List ℚ) :
    ∀ a : ℚ,
      thetaBulkSelectedGammaCellsCheck steps us S a bs = true →
      ThetaUpperRealCellCertificateChain a bs := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a hcheck
      have hs :
          thetaBulkSelectedGammaCellCheck steps us S a b = true ∧
          thetaBulkSelectedGammaCellsCheck steps us S b bs = true := by
        simpa only [thetaBulkSelectedGammaCellsCheck,
          Bool.and_eq_true] using hcheck
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs
      exact ⟨thetaBulkSelectedGammaCellCheck_sound
        steps us S a b hs.1, ih b hs.2⟩

/-- Conditional full ORIGINAL theta sign result. All numerical
obligations remain the explicit, finite Boolean expression. -/
theorem analyticMatrixPositive_of_bulk48_selected_gamma
    (steps : ℕ) (us : List ℚ) (S : Finset ℕ)
    (hcheck : thetaBulkSelectedGammaCellsCheck steps us S
      (821/2048:ℚ) (endpoints.drop 3) = true) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaBulkSelectedGammaCellsCheck_sound
      steps us S (endpoints.drop 3) (821/2048:ℚ) hcheck)

end W5
