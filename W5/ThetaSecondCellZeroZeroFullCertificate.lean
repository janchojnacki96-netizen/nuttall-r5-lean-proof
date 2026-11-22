import W5.ThetaZeroZeroSharpGaussianTail
import W5.ThetaAuditedTailRationalEnclosure

/-!
# FULL original theta (0,0) entry certified on the second cell

The first-square term is already shown, without any numerical
assumptions, to lie in the sharp rational quadratic-Gamma interval.
The TRUE remaining infinite n>=2 tail is nonnegative and bounded
by 8*exp(-24), reusing the existing n^26 geometric theorem.

The Taylor lower bound for exp(24) is from Mathlib; all subsequent
768-bit comparisons use exact rational native_decide.  This is a
real enclosure of the complete ORIGINAL thetaCoefficient x 0 0,
not just the first term or a formal truncated proxy.

The other 14 independent entries on cell 2 are not covered here.
-/

namespace W5

/-- Certified exponential bound without floating-point computation:
13 positive Taylor terms give exp(24) > 80,000,000. -/
theorem thetaEightExpNegTwentyFour_lt_oneE7 :
    (8:ℝ) * Real.exp (-24) < (1:ℝ)/10000000 := by
  have hTaylor :
      (∑ i ∈ Finset.range 13,
          (24:ℝ)^i / (i.factorial:ℝ)) ≤ Real.exp 24 :=
    Real.sum_le_exp_of_nonneg (by norm_num) 13
  have hFinite :
      (80000000:ℝ) <
        ∑ i ∈ Finset.range 13,
          (24:ℝ)^i / (i.factorial:ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hExp : (80000000:ℝ) < Real.exp 24 :=
    lt_of_lt_of_le hFinite hTaylor
  have hExpPos : 0 < Real.exp 24 := Real.exp_pos _
  have hfrac :
      (8:ℝ) / Real.exp 24 < (1:ℝ)/10000000 := by
    apply (div_lt_iff₀ hExpPos).mpr
    nlinarith
  simpa only [Real.exp_neg, div_eq_mul_inv] using hfrac

/-- The original 768-bit matrix has MORE than 1e-7 of room
above the independent first-square quadratic Gamma box.
This is an exact rational comparison of the stored candidate
data, rather than a floating-point approximation. -/
theorem thetaSecondCellB00Margin_checked :
    thetaSecondCellOneSquareZeroZeroQuadraticBox.hi +
        (1:ℚ)/10000000 ≤
      (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).hi := by
  native_decide

/-- On the ENTIRE second original rational cell, the TRUE
transcendental thetaCoefficient (0,0) is contained in the actual
768-bit audited matrix entry, including all n>=2 terms.
No per-square tail approximation, conditional transform or new
numerical-analysis axiom is assumed. -/
theorem thetaSecondCellZeroZeroFullTheta_fits_audit
    (x : ℝ)
    (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512) :
    QInterval.ContainsReal
      (thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5))
      (thetaCoefficient x (0 : Fin 5) (0 : Fin 5)) := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
  have hfirst :=
    thetaSecondCellOneSquareZeroZeroQuadraticBox_containsReal x hax hxb
  obtain ⟨htail0, htailHi⟩ :=
    thetaSecondCellZeroZeroTail_nonneg_le_exp24 x hax hxb
  have htailBound :
      thetaAuditedTail 2 x (0 : Fin 5) (0 : Fin 5) ≤
        (1:ℝ)/10000000 :=
    htailHi.trans thetaEightExpNegTwentyFour_lt_oneE7.le
  have hLoQ :=
    thetaSecondCellOneSquareZeroZeroQuadraticBox_fits_audit.1
  have hLo :
      ((thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).lo : ℝ) ≤
        (thetaSecondCellOneSquareZeroZeroQuadraticBox.lo : ℝ) := by
    exact_mod_cast hLoQ
  have hHiQ := thetaSecondCellB00Margin_checked
  have hHi :
      (thetaSecondCellOneSquareZeroZeroQuadraticBox.hi : ℝ) +
          (1:ℝ)/10000000 ≤
        ((thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).hi : ℝ) := by
    calc
      (thetaSecondCellOneSquareZeroZeroQuadraticBox.hi : ℝ) +
          (1:ℝ)/10000000 =
          ((thetaSecondCellOneSquareZeroZeroQuadraticBox.hi +
              (1:ℚ)/10000000 : ℚ) : ℝ) := by
            push_cast
            ring
      _ ≤ ((thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).hi : ℝ) := by
        exact_mod_cast hHiQ
  have hSplit :
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) =
        thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) 1 +
          thetaAuditedTail 2 x (0 : Fin 5) (0 : Fin 5) := by
    rw [thetaCoefficient_eq_audited_prefix_add_tail_unconditional
      2 x hx hx1 (0 : Fin 5) (0 : Fin 5)]
    rw [thetaAuditedPrefix_two_eq_one]
  change
    ((thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).lo : ℝ) ≤
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) ∧
    thetaCoefficient x (0 : Fin 5) (0 : Fin 5) ≤
      ((thetaAuditUpperCell_02 (0 : Fin 5) (0 : Fin 5)).hi : ℝ)
  rw [hSplit]
  constructor
  · linarith [hfirst.1]
  · linarith [hfirst.2]

end W5
