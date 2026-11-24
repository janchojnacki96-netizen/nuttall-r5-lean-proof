import W5.ThetaDirectMaterializedLDL

/-!
# Compact witness for the complete last theta cell

An independent exact Fraction replay finds all five alternating
pivots strictly signed on the slightly enlarged dyadic interval
[148367/262144,145/256], with the original twelve bins and eight
root bisections. Sharp Gamma moments for n=2 are unnecessary here:
only n=1 uses the running Gamma grid. Cache Gaussian factors for
n=2,...,6. Separate the analytic enclosure check from LDL, using
a small, explicitly outward-padded rational witness matrix.
The imported 768-bit audit matrix is not needed.

The external replay is ONLY a witness finder. The theorem below
requires all independent Lean Boolean checks to succeed.
-/

namespace W5

def thetaLastCellA : ℚ := 148367/262144
def thetaLastCellB : ℚ := 145/256
def thetaLastCellGrid : List ℚ :=
  (List.range 12).map (fun j => ((4*(j+1):ℕ):ℚ))

/-- The original Gaussian exponential is shared between the entries,
rather than recomputing its 65-term Taylor expansion per summand. -/
def thetaLastCellCachedExp (a b : ℚ) : ℕ → QInterval :=
  let cached : Array QInterval := Array.ofFn (fun n : Fin 7 =>
    if 2 ≤ n.val then thetaBulkFixedGaussianExpBox a b n.val
    else QInterval.point 1)
  fun n => if hn : n < 7 then
    cached[n]'(by simpa [cached] using hn)
  else thetaBulkFixedGaussianExpBox a b n

theorem thetaLastCellCachedExp_eq (a b : ℚ) (n : ℕ) (hn2 : 2 ≤ n) :
    thetaLastCellCachedExp a b n = thetaBulkFixedGaussianExpBox a b n := by
  by_cases hn : n < 7
  · simp [thetaLastCellCachedExp, hn, hn2]
  · simp [thetaLastCellCachedExp, hn]

def thetaLastCellTermBox
    (N1 : ThetaIntervalMatrix) (E : ℕ → QInterval)
    (a b : ℚ) (i j : Fin 5) (n : ℕ) : QInterval :=
  if n = 0 then QInterval.point 0
  else if n = 1 then N1 i j
  else thetaBulkSignedOriginalTermBox a b n i j (E n)

/-- Only n=1 requires sharp Gamma moments on the last cell. -/
def thetaLastCellN1OnlySource (steps : ℕ) (us : List ℚ)
    (a b : ℚ) : ThetaIntervalMatrix :=
  let N1 := thetaRunningMaterializedFirstSquareMatrix steps a b us (Finset.range 9)
  let E := thetaLastCellCachedExp a b
  Matrix.of (fun i j => QInterval.add
    (thetaAuditedPrefixInterval 7 (thetaLastCellTermBox N1 E a b i j))
    thetaBulkSevenTailBox)

theorem thetaLastCellN1OnlySource_containsReal
    (steps : ℕ) (us : List ℚ) (a b : ℚ) (x : ℝ)
    (ha : (0:ℚ) < a) (hx : 0 < x)
    (hax : (a:ℝ) ≤ x) (hxb : x ≤ (b:ℝ))
    (hb : (b:ℝ) ≤ (145:ℝ)/256)
    (hExp : ThetaBulkGaussianEligibility a b)
    (hA : thetaGammaAutoMomentCheck steps a us = true)
    (hB : thetaGammaAutoMomentCheck steps b us = true)
    (i j : Fin 5) :
    QInterval.ContainsReal (thetaLastCellN1OnlySource steps us a b i j)
      (thetaCoefficient x i j) := by
  have hb1 : (b:ℝ) ≤ 1 := by linarith
  have hx1 : x ≤ 1 := hxb.trans hb1
  let N1 := thetaRunningMaterializedFirstSquareMatrix steps a b us (Finset.range 9)
  let E := thetaLastCellCachedExp a b
  have hterm : ∀ n ∈ Finset.range 7,
      QInterval.ContainsReal (thetaLastCellTermBox N1 E a b i j n)
        (thetaAuditedSeriesTerm x i j n) := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [thetaLastCellTermBox, thetaAuditedSeriesTerm_zero,
        QInterval.ContainsReal, QInterval.point]
    · by_cases hn1 : n = 1
      · subst n
        have h := thetaRunningFirstSquareMatrix_containsReal
          steps a b us (Finset.range 9) x ha.le hx hax hxb hb1 hA hB i j
        simpa only [thetaLastCellTermBox, Nat.one_ne_zero, if_false, if_true,
          N1, thetaRunningMaterializedFirstSquareMatrix_eq,
          thetaRunningSharedFirstSquareMatrix_apply] using h
      · have hn2 : 2 ≤ n := by omega
        have hn7 : n < 7 := Finset.mem_range.mp hn
        simpa only [thetaLastCellTermBox, if_neg hn0, if_neg hn1, E,
          thetaLastCellCachedExp_eq a b n hn2, thetaBulkGeneratedSignedTerm]
          using thetaBulkGeneratedSignedTerm_containsReal
            a b x ha hx hax hxb hb hExp i j n hn2 hn7
  have htail := thetaBulkSevenTailBox_containsReal x hx (hxb.trans hb) i j
  change QInterval.ContainsReal
    (QInterval.add (thetaAuditedPrefixInterval 7
      (thetaLastCellTermBox N1 E a b i j)) thetaBulkSevenTailBox)
    (thetaCoefficient x i j)
  exact thetaCoefficient_containsReal_of_termwise_bounds_and_tail_unconditional
    7 x hx hx1 i j (thetaLastCellTermBox N1 E a b i j)
    (QInterval.add (thetaAuditedPrefixInterval 7
      (thetaLastCellTermBox N1 E a b i j)) thetaBulkSevenTailBox)
    thetaBulkSevenTailBox hterm htail le_rfl le_rfl

def thetaLastCellMicroBox (l u : ℤ) : QInterval :=
  ⟨(l:ℚ)/1000000, (u:ℚ)/1000000⟩

/-- Witness entries, outward padded by one additional micro-unit.
The lower triangle is filled by the existing symmetric checker. -/
def thetaLastCellWitness : ThetaIntervalMatrix :=
  Matrix.of (fun i j => match i.val, j.val with
  | 0, 0 => thetaLastCellMicroBox 914576 915221
  | 0, 1 => thetaLastCellMicroBox 48696 49605
  | 0, 2 => thetaLastCellMicroBox (-25812) (-24995)
  | 0, 3 => thetaLastCellMicroBox 9098 9712
  | 0, 4 => thetaLastCellMicroBox 360 816
  | 1, 1 => thetaLastCellMicroBox (-939166) (-936585)
  | 1, 2 => thetaLastCellMicroBox (-51356) (-48049)
  | 1, 3 => thetaLastCellMicroBox 42240 45223
  | 1, 4 => thetaLastCellMicroBox (-36717) (-34421)
  | 2, 2 => thetaLastCellMicroBox 504933 510589
  | 2, 3 => thetaLastCellMicroBox (-19950) (-13696)
  | 2, 4 => thetaLastCellMicroBox 4077 9766
  | 3, 3 => thetaLastCellMicroBox (-152922) (-144314)
  | 3, 4 => thetaLastCellMicroBox 6056 16513
  | 4, 4 => thetaLastCellMicroBox (-464) 17028
  | _, _ => QInterval.point 0)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellWitnessLDL :
    intervalLDL5AlternatingCheck (thetaSymmetricIntervals thetaLastCellWitness) = true := by
  rw [← thetaDirectLDLCheck_eq]
  native_decide

/-- Compute just the 15 independent genuine source entries, once each. -/
def thetaLastCellCachedUpperSource : ThetaIntervalMatrix :=
  let S := thetaLastCellN1OnlySource 8 thetaLastCellGrid thetaLastCellA thetaLastCellB
  thetaDirectCacheMatrix (Matrix.of (fun i j =>
    if i ≤ j then S i j else QInterval.point 0))

theorem thetaLastCellCachedUpperSource_apply (i j : Fin 5) (hij : i ≤ j) :
    thetaLastCellCachedUpperSource i j =
      thetaLastCellN1OnlySource 8 thetaLastCellGrid thetaLastCellA thetaLastCellB i j := by
  simp only [thetaLastCellCachedUpperSource, thetaDirectCacheMatrix_eq,
    Matrix.of_apply, if_pos hij]

/-- Cheaper eligibility: there are no n=2 Gamma-grid checks. -/
def thetaLastCellN1Eligible : Bool :=
  decide ((0:ℚ) < thetaLastCellA ∧ thetaLastCellA ≤ thetaLastCellB ∧
    thetaLastCellB ≤ (145:ℚ)/256 ∧
    ThetaBulkGaussianEligibility thetaLastCellA thetaLastCellB ∧
    thetaGammaAutoMomentCheck 8 thetaLastCellA thetaLastCellGrid = true ∧
    thetaGammaAutoMomentCheck 8 thetaLastCellB thetaLastCellGrid = true)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellN1Eligible_checked : thetaLastCellN1Eligible = true := by
  native_decide

/-- No #eval, no huge-denominator Schur calculation on the source:
only an exact native interval inclusion computation remains. -/
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
theorem thetaLastCellWitnessFits :
    thetaUpperMatrixRefinesCheck thetaLastCellWitness thetaLastCellCachedUpperSource = true := by
  native_decide

theorem thetaLastCellDyadicCertificate :
    ThetaUpperRealCellCertificate thetaLastCellA thetaLastCellB := by
  have h : (0:ℚ) < thetaLastCellA ∧ thetaLastCellA ≤ thetaLastCellB ∧
      thetaLastCellB ≤ (145:ℚ)/256 ∧
      ThetaBulkGaussianEligibility thetaLastCellA thetaLastCellB ∧
      thetaGammaAutoMomentCheck 8 thetaLastCellA thetaLastCellGrid = true ∧
      thetaGammaAutoMomentCheck 8 thetaLastCellB thetaLastCellGrid = true :=
    of_decide_eq_true thetaLastCellN1Eligible_checked
  rcases h with ⟨ha, _, hb, hExp, hA, hB⟩
  apply thetaUpperRealCellCertificate_of_checked thetaLastCellA thetaLastCellB
    thetaLastCellWitness thetaLastCellWitnessLDL
  intro x hx hax hxb i j hij
  have hbR : (thetaLastCellB:ℝ) ≤ (145:ℝ)/256 := by
    have hc : (thetaLastCellB:ℝ) ≤ (((145:ℚ)/256):ℝ) := by exact_mod_cast hb
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hc
  apply thetaUpperMatrixRefines_containsReal thetaLastCellWitness
    thetaLastCellCachedUpperSource
    (thetaUpperMatrixRefinesCheck_sound _ _ thetaLastCellWitnessFits)
    (thetaCoefficient x i j) i j hij
  rw [thetaLastCellCachedUpperSource_apply i j hij]
  exact thetaLastCellN1OnlySource_containsReal 8 thetaLastCellGrid
    thetaLastCellA thetaLastCellB x ha hx hax hxb hbR hExp hA hB i j

/-- The dyadic interval contains the slightly rounded original cell. -/
theorem thetaLastCellCertificate :
    ThetaUpperRealCellCertificate (endpoints.reverse.drop 1).head! endpoints.reverse.head! := by
  have ha : thetaLastCellA ≤ (endpoints.reverse.drop 1).head! := by native_decide
  have hb : endpoints.reverse.head! = thetaLastCellB := by native_decide
  obtain ⟨C, hldl, hC⟩ := thetaLastCellDyadicCertificate
  refine ⟨C, hldl, ?_⟩
  intro x hx hax hxb i j hij
  have haR : (thetaLastCellA:ℝ) ≤ (((endpoints.reverse.drop 1).head! : ℚ):ℝ) := by
    exact_mod_cast ha
  exact hC x hx (haR.trans hax) (by simpa only [hb] using hxb) i j hij

end W5
