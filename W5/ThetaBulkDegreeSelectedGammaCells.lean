import W5.ThetaGammaDegreeSelectedMoments
import W5.ThetaBulkSelectedGammaCells

/-!
# Joint n/k selective certified original theta interval engine

The n=1 term has nine Gamma moments. A finite subset K chooses the
moment degrees to evaluate with the expensive certified root/Gamma
grid, and all other k use their old proven cubic bounds. Independently
a finite set S chooses which higher terms n=2,...,6 use sharp moments.

This one generator supports ALL 25 entries and ANY finite x-cell
partition, using the exact same signed theta coefficient polynomials,
Gaussian exponential eligibility and tail. No numerical result is
assumed; the final all-cell Boolean is an explicit unproved check.
-/

namespace W5

/-- Keep the original theta term for every n, while independently
choosing high-precision Gamma degrees K at n=1 and selected n>=2
indices S. -/
def thetaBulkDegreeSelectedTermBox
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 1 then
    thetaGammaDegreeSelectedFirstSquareMatrix steps a b us K i j
  else
    thetaBulkSelectedGammaTermBox steps us S a b i j n

/-- Original 5-by-5 theta coefficient intervals with both
independent selectivity parameters, with unchanged n>=7 tail. -/
def thetaBulkDegreeSelectedCellMatrix
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkDegreeSelectedTermBox steps us K S a b i j))
      thetaBulkSevenTailBox)

/-- One proof for all k,n,i,j and all x-cells; interval selections
remain sound because both moment generators have certified real
semantics. -/
theorem thetaBulkDegreeSelectedCellMatrix_containsReal
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
      (thetaBulkDegreeSelectedCellMatrix steps us K S a b i j)
      (thetaCoefficient x i j) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal
        (thetaBulkDegreeSelectedTermBox steps us K S a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn1 : n = 1
    · subst n
      simpa [thetaBulkDegreeSelectedTermBox] using
        (thetaGammaDegreeSelectedFirstSquareMatrix_containsReal
          steps a b us K x ha.le hx hax hxb hb1 hA hB i j)
    · have hrest :
          QInterval.ContainsReal
            (thetaBulkSelectedGammaTermBox steps us S a b i j n)
            (thetaAuditedSeriesTerm x i j n) := by
        by_cases hn0 : n = 0
        · subst n
          simp [thetaBulkSelectedGammaTermBox,
            thetaAuditedSeriesTerm_zero, QInterval.ContainsReal,
            QInterval.point]
        · have hn2 : 2 ≤ n := by omega
          have hn7 : n < 7 := Finset.mem_range.mp hn
          by_cases hns : n ∈ S
          · have hs := hSel ⟨n, hn7⟩ hn2 hns
            simpa [thetaBulkSelectedGammaTermBox, hn0, hn1, hns] using
              (thetaBulkSharpHigherSquareTermBox_containsReal
                steps us a b x ha hx hax hxb hb hExp i j n
                hn2 hn7 hs.1 hs.2)
          · simpa [thetaBulkSelectedGammaTermBox, hn0, hn1, hns] using
              (thetaBulkGeneratedSignedTerm_containsReal
                a b x ha hx hax hxb hb hExp i j n hn2 hn7)
      simpa [thetaBulkDegreeSelectedTermBox, hn1] using hrest
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkDegreeSelectedTermBox steps us K S a b i j))
      thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j
    (thetaBulkDegreeSelectedTermBox steps us K S a b i j)
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaBulkDegreeSelectedTermBox steps us K S a b i j))
      thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- Finite exact rational last-pivot and eligibility check.
No noncomputable transcendental decision is made. -/
def thetaBulkDegreeSelectedCellCheck
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility steps us S a b ∧
    intervalLDL5AlternatingCheck
      (thetaSymmetricIntervals
        (thetaBulkDegreeSelectedCellMatrix steps us K S a b)) = true)

/-- Successful rational LDL computation gives an actual
real-sound original theta certificate for the complete x-cell. -/
theorem thetaBulkDegreeSelectedCellCheck_sound
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (a b : ℚ)
    (hcheck : thetaBulkDegreeSelectedCellCheck
      steps us K S a b = true) :
    ThetaUpperRealCellCertificate a b := by
  have h : (0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
      ThetaBulkGaussianEligibility a b ∧
      thetaGammaAutoMomentCheck steps a us = true ∧
      thetaGammaAutoMomentCheck steps b us = true ∧
      ThetaBulkSelectedGammaEligibility steps us S a b ∧
      intervalLDL5AlternatingCheck
        (thetaSymmetricIntervals
          (thetaBulkDegreeSelectedCellMatrix steps us K S a b)) = true :=
    of_decide_eq_true hcheck
  rcases h with ⟨ha, _, hb, hExp, hA, hB, hSel, hldl⟩
  refine ⟨thetaBulkDegreeSelectedCellMatrix steps us K S a b,
    intervalLDL5Alternating_of_check
      (thetaSymmetricIntervals
        (thetaBulkDegreeSelectedCellMatrix steps us K S a b)) hldl, ?_⟩
  intro x hx hax hxb i j _
  have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
      exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact thetaBulkDegreeSelectedCellMatrix_containsReal
    steps us K S a b x ha hx hax hxb hbR
    hExp hA hB hSel i j

/-- No per-cell proofs: traverse any finite list of rational
theta x-cell boundaries with one Boolean. -/
def thetaBulkDegreeSelectedCellsCheck
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ) :
    ℚ → List ℚ → Bool
  | _, [] => true
  | a, b :: bs =>
      thetaBulkDegreeSelectedCellCheck steps us K S a b &&
      thetaBulkDegreeSelectedCellsCheck steps us K S b bs

/-- One induction transports the rational Boolean chain to all
real theta coefficients and all five original LDL pivot signs. -/
theorem thetaBulkDegreeSelectedCellsCheck_sound
    (steps : ℕ) (us : List ℚ)
    (K S : Finset ℕ) (bs : List ℚ) :
    ∀ a : ℚ,
      thetaBulkDegreeSelectedCellsCheck steps us K S a bs = true →
      ThetaUpperRealCellCertificateChain a bs := by
  induction bs with
  | nil =>
      intro a _
      trivial
  | cons b bs ih =>
      intro a hcheck
      have hs :
          thetaBulkDegreeSelectedCellCheck steps us K S a b = true ∧
          thetaBulkDegreeSelectedCellsCheck steps us K S b bs = true := by
        simpa only [thetaBulkDegreeSelectedCellsCheck,
          Bool.and_eq_true] using hcheck
      change ThetaUpperRealCellCertificate a b ∧
        ThetaUpperRealCellCertificateChain b bs
      exact ⟨thetaBulkDegreeSelectedCellCheck_sound
        steps us K S a b hs.1, ih b hs.2⟩

/-- The original analytic theta matrix has the required five
pivot signs once (and ONLY once) the actual global rational test
has returned true. This is not a proof of W5.MainClaim. -/
theorem analyticMatrixPositive_of_bulk48_degree_selected_gamma
    (steps : ℕ) (us : List ℚ) (K S : Finset ℕ)
    (hcheck : thetaBulkDegreeSelectedCellsCheck steps us K S
      (821/2048:ℚ) (endpoints.drop 3) = true) :
    analyticMatrixPositive :=
  analyticMatrixPositive_of_remaining_48_upper_certificates
    (thetaBulkDegreeSelectedCellsCheck_sound
      steps us K S (endpoints.drop 3) (821/2048:ℚ) hcheck)

end W5
