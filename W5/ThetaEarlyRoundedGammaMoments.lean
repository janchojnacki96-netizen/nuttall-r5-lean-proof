import W5.ThetaBulkRoundedDegreeSelectedCells
import W5.ThetaMemoN1N2SelectedCellMatrix

/-!
# Early 768-bit outward rounding of exact Gamma moment intervals

The previously proved selected original theta coefficient generator
performed huge signed rational polynomial expansions BEFORE rounding
their final interval entries. The resulting numerator/denominator growth
made last-cell diagnostics exceed a 45-minute GitHub runner budget.

Here each Gamma moment is first rounded OUTWARD to the ALREADY
proven exact 2^768 rational scale. The existing QInterval real
soundness theorems are reused; early rounding cannot lose any true
Gamma integral, and the exact original n=1 and n=2 signed coefficients
are unchanged. This makes all downstream rational multiplications
work with bounded-denominator inputs rather than giant grid fractions.

No unchecked numerical output is made a theorem. Any future signed
pivot Boolean must still actually evaluate to true before it is used.
-/

namespace W5

/-- Round one existing K-selected n=1 Gamma moment, before any
polynomial multiplication; inclusion is outward and certified. -/
def thetaEarlyRoundedSelectedMoment
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) : QInterval :=
  thetaBulkRoundedQInterval
    (thetaGammaDegreeSelectedMomentBox steps a b us K k)

theorem thetaEarlyRoundedSelectedMoment_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) (x : ℝ)
    (ha : (0 : ℚ) ≤ a)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true) :
    QInterval.ContainsReal
      (thetaEarlyRoundedSelectedMoment steps a b us K k)
      (thetaAuditedOneWeightedMoment x k) := by
  exact thetaBulkRoundedQInterval_containsReal _
    (thetaAuditedOneWeightedMoment x k)
    (thetaGammaDegreeSelectedMomentBox_containsReal
      steps a b us K k x ha hax hxb hb hA hB)

/-- Cache all nine early-rounded exact rational intervals once,
and retain the same computable real-sound generator for k>=9. -/
def thetaEarlyRoundedSelectedNine
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ℕ → QInterval :=
  let cached : Array QInterval :=
    Array.ofFn (fun k : Fin 9 =>
      thetaEarlyRoundedSelectedMoment steps a b us K k.val)
  fun k =>
    if hk : k < 9 then
      cached[k]'(by simpa [cached] using hk)
    else thetaEarlyRoundedSelectedMoment steps a b us K k

theorem thetaEarlyRoundedSelectedNine_eq
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (k : ℕ) :
    thetaEarlyRoundedSelectedNine steps a b us K k =
      thetaEarlyRoundedSelectedMoment steps a b us K k := by
  by_cases hk : k < 9
  · simp [thetaEarlyRoundedSelectedNine, hk]
  · simp [thetaEarlyRoundedSelectedNine, hk]

/-- The original n=1 term, with no change except the verified
early-outward-rounded and memoized moment boxes. -/
def thetaEarlyRoundedFirstSquareMatrix
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) : ThetaIntervalMatrix :=
  let M := thetaEarlyRoundedSelectedNine steps a b us K
  Matrix.of (fun i j =>
    thetaAuditedOneTermMomentInterval
      (thetaFirstCellGammaUniformDiagonal i j)
      (thetaOneSquareCellScaleBox a b)
      (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
      M 9)

/-- Original genuine n=1 theta integral is still enclosed:
the nine-moment theorem is parameterized by ANY sound moments. -/
theorem thetaEarlyRoundedFirstSquareMatrix_containsReal
    (steps : ℕ) (a b : ℚ) (us : List ℚ)
    (K : Finset ℕ) (x : ℝ)
    (ha : (0 : ℚ) ≤ a) (hx : 0 < x)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaEarlyRoundedFirstSquareMatrix steps a b us K i j)
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
    x hx (hxb.trans hb) i j
    (thetaFirstCellGammaUniformDiagonal i j)
    (thetaOneSquareCellScaleBox a b)
    (thetaGeneralCellCubicBinomialCoefficientBox a b i j)
    (thetaEarlyRoundedSelectedNine steps a b us K)
    hdiag
    (thetaOneSquareCellScaleBox_containsReal a b x hax hxb)
    (fun k _ =>
      thetaGeneralCellCubicBinomialCoefficientBox_containsReal
        a b x hax hxb i j k)
    (fun k _ => by
      rw [thetaEarlyRoundedSelectedNine_eq]
      exact thetaEarlyRoundedSelectedMoment_containsReal
        steps a b us K k x ha hax hxb hb hA hB)

/-- Round one genuine n-th Gamma moment before expensive signed
correction expansion; applies uniformly at all n,k. -/
def thetaEarlyRoundedAutoMoment
    (steps k : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) : QInterval :=
  thetaBulkRoundedQInterval
    (thetaGammaAutoCellMomentBox steps k a b n us)

theorem thetaEarlyRoundedAutoMoment_containsReal
    (steps k : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (x : ℝ)
    (ha : (0 : ℚ) ≤ a) (hn : 0 < n)
    (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ 1)
    (hA : thetaGammaAutoMomentCheck
      steps (a / (n : ℚ)) us = true)
    (hB : thetaGammaAutoMomentCheck
      steps (b / (n : ℚ)) us = true) :
    QInterval.ContainsReal
      (thetaEarlyRoundedAutoMoment steps k a b n us)
      (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) := by
  exact thetaBulkRoundedQInterval_containsReal _
    (thetaAuditedOneWeightedMoment (x/(n:ℝ)) k)
    (thetaGammaAutoCellMomentBox_containsReal
      steps k a b n us x ha hn hax hxb hb hA hB)

/-- The first nine n=2 moments appear repeatedly in the signed
double-binomial expansion: use one memo array for all coefficients. -/
def thetaEarlyRoundedAutoNine
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) : ℕ → QInterval :=
  let cached : Array QInterval :=
    Array.ofFn (fun k : Fin 9 =>
      thetaEarlyRoundedAutoMoment steps k.val a b n us)
  fun k =>
    if hk : k < 9 then
      cached[k]'(by simpa [cached] using hk)
    else thetaEarlyRoundedAutoMoment steps k a b n us

theorem thetaEarlyRoundedAutoNine_eq
    (steps : ℕ) (a b : ℚ) (n : ℕ)
    (us : List ℚ) (k : ℕ) :
    thetaEarlyRoundedAutoNine steps a b n us k =
      thetaEarlyRoundedAutoMoment steps k a b n us := by
  by_cases hk : k < 9
  · simp [thetaEarlyRoundedAutoNine, hk]
  · simp [thetaEarlyRoundedAutoNine, hk]

def thetaEarlyRoundedN2Matrix
    (steps : ℕ) (us : List ℚ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let E := thetaBulkFixedGaussianExpBox a b 2
  let M := thetaEarlyRoundedAutoNine steps a b 2 us
  Matrix.of (fun i j =>
    thetaBulkSignedParameterizedTermBox a b 2 i j E M)

/-- The original REAL signed n=2 term is still enclosed after
early rounding every input Gamma moment. -/
theorem thetaEarlyRoundedN2Matrix_containsReal
    (steps : ℕ) (us : List ℚ) (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hSel : ThetaBulkSelectedGammaEligibility
      steps us ({2} : Finset ℕ) a b)
    (i j : Fin 5) :
    QInterval.ContainsReal
      (thetaEarlyRoundedN2Matrix steps us a b i j)
      (thetaAuditedSeriesTerm x i j 2) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hEl := hExp ⟨2, by norm_num⟩ (by norm_num : 2 ≤ (2:ℕ))
  have hE := thetaBulkFixedGaussianExpBox_containsReal
    a b x 2 ha hax hxb (by norm_num) hEl.1 hEl.2
  have hAB := hSel ⟨2, by norm_num⟩
    (by norm_num : 2 ≤ (2:ℕ)) (by simp)
  have hM : ∀ k : ℕ,
      QInterval.ContainsReal
        (thetaEarlyRoundedAutoNine steps a b 2 us k)
        (thetaAuditedOneWeightedMoment (x/(2:ℝ)) k) := by
    intro k
    rw [thetaEarlyRoundedAutoNine_eq]
    exact thetaEarlyRoundedAutoMoment_containsReal
      steps k a b 2 us x ha.le (by norm_num)
      hax hxb hb1 hAB.1 hAB.2
  change QInterval.ContainsReal
    (thetaBulkSignedParameterizedTermBox a b 2 i j
      (thetaBulkFixedGaussianExpBox a b 2)
      (thetaEarlyRoundedAutoNine steps a b 2 us))
    (thetaAuditedSeriesTerm x i j 2)
  exact thetaBulkSignedParameterizedTermBox_containsReal
    a b x ha hx hax hxb hb1 i j 2 (by norm_num)
    (thetaBulkFixedGaussianExpBox a b 2) hE
    (thetaEarlyRoundedAutoNine steps a b 2 us) hM

end W5
