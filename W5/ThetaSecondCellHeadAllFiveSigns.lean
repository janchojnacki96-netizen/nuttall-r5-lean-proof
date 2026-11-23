import W5.ThetaSecondCellHeadKSoundness
import W5.ThetaSecondCellHeadGaussianFactor
import W5.ThetaSecondCellTwoTermReduction

/-!
# Close the complete ORIGINAL second x-cell from two finite head indices

All computational rational K caps were already native_decide checked
in ThetaSecondCellHeadFiniteMajorants. The n>=4 true theta tail and
the padded 5x5 exact rational LDL check are already compiled.

Here we ONLY compose:
- the new universal real-sound original n-th term bound;
- four existing 25-entry rational K cap checks;
- three existing Mathlib Taylor bounds for exp(-E);
- one existing true-tail reduction to n=2 and n=3.

No new quadrature, new matrix, per-entry case split or determinant
factorization is introduced. This file is a CANDIDATE until Lean CI.
-/

namespace W5

private theorem thetaSecondCell_two_small_first_subcell
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x) (hxb : x ≤ (1:ℝ)/4)
    (i j : Fin 5) :
    |thetaAuditedSeriesTerm x i j 2| ≤ (1:ℝ)/200 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have haxQ : ((1/8:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hax
  have hxbQ : x ≤ ((1/4:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hxb
  have hReal :=
    thetaHead_originalSeriesTerm_abs_le_rationalK
      (1/8) (1/4) x 2 (by omega) i j
      (by norm_num) haxQ hxbQ (by norm_num)
  have hK :=
    (thetaSecondCellHeadPositiveMajorants_checked i j).1
  have h :=
    thetaHeadTerm_abs_le_of_rational_majorant
      (1/8) (1/4) 1000000000 2 x 48
      (1/(10:ℝ)^18) i j
      hx hxbQ (by norm_num) (by norm_num)
      (by norm_num) hK hReal thetaExpNeg48_lt_oneE18.le
  exact h.trans (by norm_num)

private theorem thetaSecondCell_two_small_second_subcell
    (x : ℝ) (hax : (1:ℝ)/4 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (i j : Fin 5) :
    |thetaAuditedSeriesTerm x i j 2| ≤ (1:ℝ)/200 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have haxQ : ((1/4:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hax
  have hxbQ : x ≤ ((177/512:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  have hReal :=
    thetaHead_originalSeriesTerm_abs_le_rationalK
      (1/4) (177/512) x 2 (by omega) i j
      (by norm_num) haxQ hxbQ (by norm_num)
  have hK :=
    (thetaSecondCellHeadPositiveMajorants_checked i j).2.1
  have h :=
    thetaHeadTerm_abs_le_of_rational_majorant
      (1/4) (177/512) 5000000 2 x 25
      (1/(10:ℝ)^9) i j
      hx hxbQ (by norm_num) (by norm_num)
      (by norm_num) hK hReal thetaExpNeg25_lt_oneE9.le
  exact h.trans (by norm_num)

private theorem thetaSecondCell_three_small_first_subcell
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x) (hxb : x ≤ (1:ℝ)/4)
    (i j : Fin 5) :
    |thetaAuditedSeriesTerm x i j 3| ≤ 1/(10:ℝ)^12 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have haxQ : ((1/8:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hax
  have hxbQ : x ≤ ((1/4:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hxb
  have hReal :=
    thetaHead_originalSeriesTerm_abs_le_rationalK
      (1/8) (1/4) x 3 (by omega) i j
      (by norm_num) haxQ hxbQ (by norm_num)
  have hK :=
    (thetaSecondCellHeadPositiveMajorants_checked i j).2.2.1
  have h :=
    thetaHeadTerm_abs_le_of_rational_majorant
      (1/8) (1/4) 5000000000000 3 x 64
      (1/(10:ℝ)^25) i j
      hx hxbQ (by norm_num) (by norm_num)
      (by norm_num) hK hReal thetaExpNeg64_lt_oneE25.le
  exact h.trans (by norm_num)

private theorem thetaSecondCell_three_small_second_subcell
    (x : ℝ) (hax : (1:ℝ)/4 ≤ x)
    (hxb : x ≤ (177:ℝ)/512)
    (i j : Fin 5) :
    |thetaAuditedSeriesTerm x i j 3| ≤ 1/(10:ℝ)^12 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have haxQ : ((1/4:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hax
  have hxbQ : x ≤ ((177/512:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  have hReal :=
    thetaHead_originalSeriesTerm_abs_le_rationalK
      (1/4) (177/512) x 3 (by omega) i j
      (by norm_num) haxQ hxbQ (by norm_num)
  have hK :=
    (thetaSecondCellHeadPositiveMajorants_checked i j).2.2.2
  have h :=
    thetaHeadTerm_abs_le_of_rational_majorant
      (1/4) (177/512) 20000000000 3 x 64
      (1/(10:ℝ)^25) i j
      hx hxbQ (by norm_num) (by norm_num)
      (by norm_num) hK hReal thetaExpNeg64_lt_oneE25.le
  exact h.trans (by norm_num)

/-- Complete uniform real original n=2,3 term bounds in the second
audited theta cell, proved without repeating any entry calculation. -/
theorem thetaSecondCell_unconditional_two_three_abs_bounds
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512) :
    (∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 2| ≤ (1:ℝ)/200) ∧
    (∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 3| ≤ 1/(10:ℝ)^12) := by
  by_cases hquarter : x ≤ (1:ℝ)/4
  · exact
      ⟨fun i j => thetaSecondCell_two_small_first_subcell
        x hax hquarter i j,
       fun i j => thetaSecondCell_three_small_first_subcell
        x hax hquarter i j⟩
  · have hquarter' : (1:ℝ)/4 ≤ x := by linarith
    exact
      ⟨fun i j => thetaSecondCell_two_small_second_subcell
        x hquarter' hxb i j,
       fun i j => thetaSecondCell_three_small_second_subcell
        x hquarter' hxb i j⟩

/-- Final REAL five-pivot theorem for the ORIGINAL full theta
coefficient matrix on the entire second cell. This invokes the
previously checked rational padded LDL matrix and genuine n>=4 tail,
after discharging its only two scalar analytic premises. -/
theorem thetaSecondCell_unconditional_allFivePivotSigns
    (x : ℝ) (hax : (1:ℝ)/8 ≤ x)
    (hxb : x ≤ (177:ℝ)/512) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  rcases thetaSecondCell_unconditional_two_three_abs_bounds
    x hax hxb with ⟨h2, h3⟩
  exact thetaSecondCell_allFivePivotSigns_of_two_term_bounds
    x hax hxb h2 h3

end W5
