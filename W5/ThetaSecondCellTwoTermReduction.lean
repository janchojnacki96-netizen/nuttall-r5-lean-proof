import W5.ThetaSecondCellAllEntriesTailFour
import W5.ThetaSecondCellCubicRealPivotBridge

/-!
# A single two-term analytic reduction for the SECOND x-cell

The original theta coefficient is an ACTUAL convergent infinite
series. We re-use the existing unconditional prefix/tail equality
TWICE, at N=2 and N=4, to reduce the full n>=2 tail to exactly
the genuine n=2 and n=3 terms plus the ALREADY proved n>=4 tail.

No reindexing sum proof or determinant proof is recreated.
Once two common scalar bounds for n=2,3 are proved by the
positive binomial/Gamma majorant, the existing exact-rational
widened LDL checker gives the REAL full second-cell pivot signs.
-/

namespace W5

/-- A finite prefix subtraction, using existing unrestricted
theta-series summability and exact prefix/tail identities. -/
theorem thetaSecondCell_tail_two_eq_two_terms_add_tail_four
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) :
    thetaAuditedTail 2 x i j =
      thetaAuditedSeriesTerm x i j 2 +
      thetaAuditedSeriesTerm x i j 3 +
      thetaAuditedTail 4 x i j := by
  have h2 := thetaCoefficient_eq_audited_prefix_add_tail_unconditional
    2 x hx hx1 i j
  have h4 := thetaCoefficient_eq_audited_prefix_add_tail_unconditional
    4 x hx hx1 i j
  have hprefix :
      thetaAuditedPrefix 4 x i j =
        thetaAuditedPrefix 2 x i j +
          thetaAuditedSeriesTerm x i j 2 +
          thetaAuditedSeriesTerm x i j 3 := by
    simp [thetaAuditedPrefix, Finset.sum_range_succ]
  linarith

/-- Common n=2 and n=3 term bounds are enough for the complete
genuine n>=2 tail on the whole second audited cell. -/
theorem thetaSecondCell_tail_two_abs_lt_oneHundred
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (i j : Fin 5)
    (h2 : |thetaAuditedSeriesTerm x i j 2| ≤ (1:ℝ)/200)
    (h3 : |thetaAuditedSeriesTerm x i j 3| ≤
      1/(10:ℝ)^12) :
    |thetaAuditedTail 2 x i j| < (1:ℝ)/100 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
  have htail4 :=
    thetaSecondCell_allEntriesTail_four_abs_lt_oneE12
      x hx hxb i j
  rw [thetaSecondCell_tail_two_eq_two_terms_add_tail_four
      x hx hx1 i j]
  have htriangle :
      |thetaAuditedSeriesTerm x i j 2 +
         thetaAuditedSeriesTerm x i j 3 +
         thetaAuditedTail 4 x i j| ≤
      |thetaAuditedSeriesTerm x i j 2| +
         |thetaAuditedSeriesTerm x i j 3| +
         |thetaAuditedTail 4 x i j| := by
    calc
      _ ≤ |thetaAuditedSeriesTerm x i j 2 +
           thetaAuditedSeriesTerm x i j 3| +
           |thetaAuditedTail 4 x i j| := abs_add_le _ _
      _ ≤ _ := by
        have hab := abs_add_le
          (thetaAuditedSeriesTerm x i j 2)
          (thetaAuditedSeriesTerm x i j 3)
        linarith
  have hn : (1:ℝ)/200 + 2/(10:ℝ)^12 < 1/100 := by
    norm_num
  linarith

/-- Full REAL five-pivot signs follow from only TWO
universal n=2,n=3 analytic inequalities, without an extra
integral or numerical interval computation at this stage. -/
theorem thetaSecondCell_allFivePivotSigns_of_two_term_bounds
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (h2 : ∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 2| ≤ (1:ℝ)/200)
    (h3 : ∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 3| ≤ 1/(10:ℝ)^12) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  apply thetaSecondCellCubicRealPivotSigns_of_tail x hax hxb
  intro i j
  exact (thetaSecondCell_tail_two_abs_lt_oneHundred
    x hax hxb i j (h2 i j) (h3 i j)).le

end W5
