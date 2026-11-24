import W5.ThetaGammaRunningCellMoments
import W5.ThetaGenericAuditedSubgridChecker

/-!
# True original theta matrix with fast per-bin rounded Gamma integrals

The original n=1/n=2 25-entry source is rebuilt using the already
verified running 768-bit Gamma accumulators. The n>=3, n<=6 terms
and rigorous infinite n>=7 tail are unchanged. The ONE existing
original theta soundness proof is reused: all REAL analytic theta
coefficients are contained under the same fully rational eligibility
predicates. No sign conclusion follows until the 48-cell finite audit
is evaluated and actually returns true.

The original proof patterns have been reused verbatim to avoid new
integration or Wronskian algebra; the only new input is the sound
running Gamma cell moment oracle.
-/

namespace W5

/-- One ORIGINAL n=1 matrix whose moment accuracy can be tuned
independently for k=0,...,8. All 25 entries share this evaluator. -/
def thetaRunningFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ThetaIntervalMatrix :=
  fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      (thetaGammaRunningSelectedMomentBox steps a b us K) 9

/-- One proof covers EVERY coefficient and EVERY selection of
moment degrees K. It reuses the existing nine-moment signed
interval theorem and never changes the theta integrand. -/
theorem thetaRunningFirstSquareMatrix_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (x : ℝ)
    (ha : (0:ℚ) ≤ a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb1 : (b:ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaRunningFirstSquareMatrix steps a b us K i j)
      (thetaAuditedSeriesTerm x i j 1) := by
  have hdiag : QInterval.ContainsReal
      (thetaFirstCellGammaUniformDiagonal i j)
      (if i = j then
        (-1 : ℝ)^i.val / (Nat.factorial i.val : ℝ)
       else 0) := by
    by_cases hij : i = j
    · subst j
      simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, Rat.cast_div, Rat.cast_pow]
    · simp [thetaFirstCellGammaUniformDiagonal,
        QInterval.ContainsReal, hij]
  exact thetaAuditedOneTermNineMomentInterval_containsReal
    x hx (hxb.trans hb1) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
    (thetaGammaRunningSelectedMomentBox steps a b us K)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaGeneralCellCubicBinomialCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ =>
      thetaGammaRunningSelectedMomentBox_containsReal
        steps a b us K k x ha hax hxb hb1 hA hB)


def thetaRunningAutoNine
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) : ℕ → QInterval :=
  let cached : Array QInterval :=
    Array.ofFn (fun k : Fin 9 =>
      thetaGammaRunningRoundedCellMomentBox steps k.val a b n us)
  fun k =>
    if hk : k < 9 then
      cached[k]'(by simpa [cached] using hk)
    else thetaGammaRunningRoundedCellMomentBox steps k a b n us

theorem thetaRunningAutoNine_eq
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (k : ℕ) :
    thetaRunningAutoNine steps a b n us k =
      thetaGammaRunningRoundedCellMomentBox steps k a b n us := by
  by_cases hk : k < 9
  · simp [thetaRunningAutoNine, hk]
  · simp [thetaRunningAutoNine, hk]


def thetaRunningN2Matrix
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let E := thetaBulkFixedGaussianExpBox a b 2
  let M := thetaRunningAutoNine steps a b 2 us
  Matrix.of (fun i j =>
    thetaBulkSignedParameterizedTermBox a b 2 i j E M)

/-- The original REAL signed n=2 term is still enclosed after
early rounding every input Gamma moment. -/
theorem thetaRunningN2Matrix_containsReal
    (steps : ℕ) (us : List ℚ) (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hSel : ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaRunningN2Matrix steps us a b i j)
      (thetaAuditedSeriesTerm x i j 2) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hEl := hExp ⟨2, by norm_num⟩ (by norm_num : 2 ≤ (2:ℕ))
  have hE := thetaBulkFixedGaussianExpBox_containsReal
    a b x 2 ha hax hxb (by norm_num) hEl.1 hEl.2
  have hAB := hSel ⟨2, by norm_num⟩
    (by norm_num : 2 ≤ (2:ℕ)) (by simp)
  have hM : ∀ k : ℕ,
      QInterval.ContainsReal
        (thetaRunningAutoNine steps a b 2 us k)
        (thetaAuditedOneWeightedMoment (x/(2:ℝ)) k) := by
    intro k
    rw [thetaRunningAutoNine_eq]
    exact thetaGammaRunningRoundedCellMomentBox_containsReal
      steps k a b 2 us x ha.le (by norm_num)
      hax hxb hb1 hAB.1 hAB.2
  change QInterval.ContainsReal
    (thetaBulkSignedParameterizedTermBox a b 2 i j
      (thetaBulkFixedGaussianExpBox a b 2)
      (thetaRunningAutoNine steps a b 2 us))
    (thetaAuditedSeriesTerm x i j 2)
  exact thetaBulkSignedParameterizedTermBox_containsReal
    a b x ha hx hax hxb hb1 i j 2 (by norm_num)
    (thetaBulkFixedGaussianExpBox a b 2) hE
    (thetaRunningAutoNine steps a b 2 us) hM


/-- The original seven-term prefix: zero at n=0, early-rounded
true Gamma n=1 and n=2, old certified signed terms for n>=3. -/
def thetaRunningBothTermBox
    (N1 N2 : ThetaIntervalMatrix) (a b : ℚ)
    (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else if n = 1 then N1 i j
  else if n = 2 then N2 i j
  else thetaBulkGeneratedSignedTerm a b i j n

/-- One shared pair of n=1/n=2 memo matrices is used for all
25 coefficient entries and the old n>=7 tail remains unchanged. -/
def thetaRunningBothCellMatrix
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N1 := thetaRunningFirstSquareMatrix steps a b us K
  let N2 := thetaRunningN2Matrix steps us a b
  Matrix.of (fun i j =>
    QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaRunningBothTermBox N1 N2 a b i j))
      thetaBulkSevenTailBox)

/-- Soundness over REAL theta coefficients follows from the
two early-rounding lemmas and the already established original
n>=3 signed Gaussian envelope and uniform n>=7 tail bound. -/
theorem thetaRunningBothCellMatrix_containsReal
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (hSel : ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaRunningBothCellMatrix steps us K a b i j)
      (thetaCoefficient x i j) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := by linarith
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal
        (thetaRunningBothTermBox
          (thetaRunningFirstSquareMatrix steps a b us K)
          (thetaRunningN2Matrix steps us a b) a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [thetaRunningBothTermBox,
        thetaAuditedSeriesTerm_zero, QInterval.ContainsReal,
        QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        simpa [thetaRunningBothTermBox] using
          (thetaRunningFirstSquareMatrix_containsReal
            steps a b us K x ha.le hx hax hxb hb1 hA hB i j)
      · by_cases hn2 : n = 2
        · subst n
          simpa [thetaRunningBothTermBox] using
            (thetaRunningN2Matrix_containsReal
              steps us a b x ha hx hax hxb hb
              hExp hSel i j)
        · have hn2lb : 2 ≤ n := by omega
          have hn7 : n < 7 := Finset.mem_range.mp hn
          simpa [thetaRunningBothTermBox, hn0, hn1, hn2] using
            (thetaBulkGeneratedSignedTerm_containsReal
              a b x ha hx hax hxb hb hExp i j n hn2lb hn7)
  have htail : QInterval.ContainsReal thetaBulkSevenTailBox
      (thetaAuditedTail 7 x i j) :=
    thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaRunningBothTermBox
          (thetaRunningFirstSquareMatrix steps a b us K)
          (thetaRunningN2Matrix steps us a b) a b i j))
      thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j
    (thetaRunningBothTermBox
      (thetaRunningFirstSquareMatrix steps a b us K)
      (thetaRunningN2Matrix steps us a b) a b i j)
    (QInterval.add
      (thetaAuditedPrefixInterval 7
        (thetaRunningBothTermBox
          (thetaRunningFirstSquareMatrix steps a b us K)
          (thetaRunningN2Matrix steps us a b) a b i j))
      thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

/-- Exact-rational eligibility + original audited enclosure check
for a single x-cell; NO Schur LDL recomputation is necessary.
This is a Boolean diagnostic, not a certified numerical outcome. -/
def thetaRunningBothCellAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  decide ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility a b ∧
    thetaGammaAutoMomentCheck steps a us = true ∧
    thetaGammaAutoMomentCheck steps b us = true ∧
    ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b) &&
  thetaUpperMatrixRefinesCheck target
    (thetaRunningBothCellMatrix steps us K a b)

/-- A successful executable Boolean means that the SAME audited
target matrix encloses every original REAL theta coefficient
throughout the specified cell. -/
theorem thetaRunningBothCellAuditCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ)
    (hcheck : thetaRunningBothCellAuditCheck
      steps us K target a b = true) :
    ∀ x : ℝ, 0 < x → (a:ℝ) ≤ x → x ≤ (b:ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j)
          (thetaCoefficient x i j) := by
  have hh :
      ((0:ℚ) < a ∧ a ≤ b ∧ b ≤ (145:ℚ)/256 ∧
        ThetaBulkGaussianEligibility a b ∧
        thetaGammaAutoMomentCheck steps a us = true ∧
        thetaGammaAutoMomentCheck steps b us = true ∧
        ThetaBulkSelectedGammaEligibility
          steps us ({2} : Finset ℕ) a b) ∧
      thetaUpperMatrixRefinesCheck target
        (thetaRunningBothCellMatrix
          steps us K a b) = true := by
    simpa only [thetaRunningBothCellAuditCheck,
      Bool.and_eq_true, decide_eq_true_eq] using hcheck
  rcases hh with ⟨⟨ha, _, hb, hExp, hA, hB, hSel⟩, hfit⟩
  intro x hx hax hxb i j hij
  have hbR : (b:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (b:ℝ) ≤ (((145:ℚ)/256):ℝ) := by
      exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  exact thetaUpperMatrixRefines_containsReal
    target (thetaRunningBothCellMatrix steps us K a b)
    (thetaUpperMatrixRefinesCheck_sound _ _ hfit)
    (thetaCoefficient x i j) i j hij
    (thetaRunningBothCellMatrix_containsReal
      steps us K a b x ha hx hax hxb hbR
      hExp hA hB hSel i j)


/-- Prioritize the two restrictive matrix entries before spending time
on the other thirteen comparisons. This changes no real semantics. -/
def thetaRunningPriorityAuditCheck
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ) : Bool :=
  let source := thetaRunningBothCellMatrix steps us K a b
  decide ((target 4 4).lo ≤ (source 4 4).lo ∧
    (source 4 4).hi ≤ (target 4 4).hi) &&
  decide ((target 3 4).lo ≤ (source 3 4).lo ∧
    (source 3 4).hi ≤ (target 3 4).hi) &&
  thetaRunningBothCellAuditCheck steps us K target a b

theorem thetaRunningPriorityAuditCheck_sound
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (target : ThetaIntervalMatrix) (a b : ℚ)
    (h : thetaRunningPriorityAuditCheck steps us K target a b = true) :
    ∀ x : ℝ, 0 < x → (a:ℝ) ≤ x → x ≤ (b:ℝ) →
      ∀ i j : Fin 5, i ≤ j →
        QInterval.ContainsReal (target i j) (thetaCoefficient x i j) := by
  have hmain : thetaRunningBothCellAuditCheck
      steps us K target a b = true := by
    simp only [thetaRunningPriorityAuditCheck,
      Bool.and_eq_true] at h
    exact h.2
  exact thetaRunningBothCellAuditCheck_sound steps us K target a b hmain

/-- The existing generic 48-cell soundness bridge accepts the faster
per-bin-rounded real-sound evaluator without any new cellwise proof. -/
def thetaRunningPriority48Check
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ)) : Bool :=
  thetaGenericAuditedSubgridsCheck
    (thetaRunningPriorityAuditCheck steps us K)
    (821/2048 : ℚ) (endpoints.drop 3)
    (thetaAuditUpperCellMatrices.drop 3) grids

/-- Strict conditional certificate. The 48-cell finite Boolean is NOT
yet known true; this lemma does not establish W5.MainClaim. -/
theorem analyticMatrixPositive_of_running_priority48
    (steps : ℕ) (us : List ℚ) (K : Finset ℕ)
    (grids : List (List ℚ))
    (h : thetaRunningPriority48Check steps us K grids = true) :
    analyticMatrixPositive := by
  apply analyticMatrixPositive_of_remaining_48_audited_enclosures
  exact thetaGenericAuditedSubgridsCheck_sound
    (thetaRunningPriorityAuditCheck steps us K)
    (fun target a b =>
      thetaRunningPriorityAuditCheck_sound steps us K target a b)
    (endpoints.drop 3) (821/2048 : ℚ)
    (thetaAuditUpperCellMatrices.drop 3) grids h

end W5
