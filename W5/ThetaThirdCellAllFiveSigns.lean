import W5.ThetaGenericCubicGammaCellCertificate
import W5.ThetaThirdCellTailFive
import W5.ThetaSecondCellHeadKSoundness
import W5.ThetaSecondCellHeadGaussianFactor
import W5.ThetaSecondCellTwoTermReduction

/-!
# Original Nuttall theta matrix: unconditional third x-cell signs

Extend the same genuine n-th term K domination mechanism used in
the CI-green second-cell proof. The only new closed real exponential
estimate is exp(-37/2)<10^-8; this is a finite Mathlib Taylor sum.

The third [177/512,821/2048] cell uses:
* n=1: general real-sound cubic-Gamma matrix (separate #143);
* n=2,3,4: original positive factorial K majorants, with
  finite rational native_decide and Mathlib exponential estimates;
* n>=5: one uniform genuine theta tail <10^-12 (separate #144);
* existing 5-pivot exact rational interval LDL checker (#143).

No new integration, series differentiation, numeric quadrature,
assumed matrix entry enclosures, or external untrusted certificates.
This is a candidate until the entire Lean build is green.
-/

namespace W5

/-- The third-cell n=2 exponential requires a sharper finite
Taylor sum than a single term: exp(37/2)>10^8. -/
private theorem thetaThirdCell_exp_neg_37_halves_lt_oneE8 :
    Real.exp (-(37/2:ℝ)) < 1/(10:ℝ)^8 := by
  have hfinite :
      (10:ℝ)^8 <
        ∑ k ∈ Finset.range 30,
          (37/2:ℝ)^k/(Nat.factorial k:ℝ) := by
    norm_num [Finset.sum_range_succ]
  have hE :
      (10:ℝ)^8 < Real.exp (37/2) :=
    hfinite.trans_le (Real.sum_le_exp_of_nonneg (by norm_num) 30)
  have hInv : (1:ℝ)/Real.exp (37/2) < 1/(10:ℝ)^8 := by
    apply (div_lt_div_iff₀ (Real.exp_pos _) (by positivity)).2
    simpa only [one_mul] using hE
  simpa only [Real.exp_neg, one_div] using hInv

/-- Two simple high-negative-exponent bounds from the Mathlib
one-term factorial lower estimate. -/
private theorem thetaThirdCell_exp_neg_49_lt_oneE19 :
    Real.exp (-49) < 1/(10:ℝ)^19 := by
  have hfinite :
      (10:ℝ)^19 < (49:ℝ)^49 / (Nat.factorial 49 : ℝ) := by
    norm_num
  have hE : (10:ℝ)^19 < Real.exp 49 :=
    hfinite.trans_le
      (Real.pow_div_factorial_le_exp 49 (by norm_num) 49)
  have hInv : (1:ℝ)/Real.exp 49 < 1/(10:ℝ)^19 := by
    apply (div_lt_div_iff₀ (Real.exp_pos _) (by positivity)).2
    simpa only [one_mul] using hE
  simpa only [Real.exp_neg, one_div] using hInv

private theorem thetaThirdCell_exp_neg_60_lt_oneE24 :
    Real.exp (-60) < 1/(10:ℝ)^24 := by
  have hfinite :
      (10:ℝ)^24 < (60:ℝ)^60 / (Nat.factorial 60 : ℝ) := by
    norm_num
  have hE : (10:ℝ)^24 < Real.exp 60 :=
    hfinite.trans_le
      (Real.pow_div_factorial_le_exp 60 (by norm_num) 60)
  have hInv : (1:ℝ)/Real.exp 60 < 1/(10:ℝ)^24 := by
    apply (div_lt_div_iff₀ (Real.exp_pos _) (by positivity)).2
    simpa only [one_mul] using hE
  simpa only [Real.exp_neg, one_div] using hInv

/-- One reusable transfer of genuine K dominance to an original
theta term of ANY square index on the third rational x-cell. -/
private theorem thetaThirdCell_term_abs_le
    (n : ℕ) (hn : 1 ≤ n) (C : ℚ)
    (E δ : ℝ)
    (hE : 0 ≤ E)
    (hEcap : E * ((821/2048:ℚ):ℝ)^2 ≤ (n:ℝ)^2-1)
    (hC : 0 ≤ (C:ℝ))
    (hK : ∀ i j : Fin 5,
      thetaHeadPositiveMajorant (177/512) (821/2048) n i j ≤ C)
    (hExp : Real.exp (-E) ≤ δ)
    (x : ℝ) (hax : (177:ℝ)/512 ≤ x)
    (hxb : x ≤ (821:ℝ)/2048) (i j : Fin 5) :
    |thetaAuditedSeriesTerm x i j n| ≤ (C:ℝ)*δ := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have haxQ : ((177/512:ℚ):ℝ) ≤ x := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hax
  have hxbQ : x ≤ ((821/2048:ℚ):ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using hxb
  have hReal :=
    thetaHead_originalSeriesTerm_abs_le_rationalK
      (177/512) (821/2048) x n hn i j
      (by norm_num) haxQ hxbQ (by norm_num)
  exact thetaHeadTerm_abs_le_of_rational_majorant
    (177/512) (821/2048) C n x E δ i j
    hx hxbQ hE hEcap hC (hK i j) hReal hExp

/-- The n=2,3,4 part of the ACTUAL theta series is controlled for
all 25 entries by three exact rational K caps and the above exp
bounds. Every sign and integral has already been justified. -/
theorem thetaThirdCell_three_head_abs_bounds
    (x : ℝ) (hax : (177:ℝ)/512 ≤ x)
    (hxb : x ≤ (821:ℝ)/2048) :
    (∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 2| ≤ (1:ℝ)/200) ∧
    (∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 3| ≤ 1/(10:ℝ)^9) ∧
    (∀ i j : Fin 5,
      |thetaAuditedSeriesTerm x i j 4| ≤ 1/(10:ℝ)^12) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    have h := thetaThirdCell_term_abs_le
      2 (by omega) 500000 (37/2) (1/(10:ℝ)^8)
      (by norm_num) (by norm_num) (by norm_num)
      (fun k l => (thetaThirdCellHeadPositiveMajorants_checked k l).1)
      thetaThirdCell_exp_neg_37_halves_lt_oneE8.le
      x hax hxb i j
    exact h.trans (by norm_num)
  · intro i j
    have h := thetaThirdCell_term_abs_le
      3 (by omega) 2000000000 49 (1/(10:ℝ)^19)
      (by norm_num) (by norm_num) (by norm_num)
      (fun k l => (thetaThirdCellHeadPositiveMajorants_checked k l).2.1)
      thetaThirdCell_exp_neg_49_lt_oneE19.le
      x hax hxb i j
    exact h.trans (by norm_num)
  · intro i j
    have h := thetaThirdCell_term_abs_le
      4 (by omega) 400000000000 60 (1/(10:ℝ)^24)
      (by norm_num) (by norm_num) (by norm_num)
      (fun k l => (thetaThirdCellHeadPositiveMajorants_checked k l).2.2)
      thetaThirdCell_exp_neg_60_lt_oneE24.le
      x hax hxb i j
    exact h.trans (by norm_num)

/-- Reuse the EXISTING complete original theta prefix/tail
identities: the tail at 2 is exactly three head terms and tail5. -/
theorem thetaThirdCell_tail_two_eq_three_terms_add_tail_five
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) (i j : Fin 5) :
    thetaAuditedTail 2 x i j =
      thetaAuditedSeriesTerm x i j 2 +
      thetaAuditedSeriesTerm x i j 3 +
      thetaAuditedSeriesTerm x i j 4 +
      thetaAuditedTail 5 x i j := by
  have h4 :=
    thetaCoefficient_eq_audited_prefix_add_tail_unconditional
      4 x hx hx1 i j
  have h5 :=
    thetaCoefficient_eq_audited_prefix_add_tail_unconditional
      5 x hx hx1 i j
  have hprefix :
      thetaAuditedPrefix 5 x i j =
        thetaAuditedPrefix 4 x i j +
          thetaAuditedSeriesTerm x i j 4 := by
    simp [thetaAuditedPrefix, Finset.sum_range_succ]
  have h45 : thetaAuditedTail 4 x i j =
      thetaAuditedSeriesTerm x i j 4 +
        thetaAuditedTail 5 x i j := by
    linarith
  calc
    thetaAuditedTail 2 x i j =
      thetaAuditedSeriesTerm x i j 2 +
        thetaAuditedSeriesTerm x i j 3 +
        thetaAuditedTail 4 x i j :=
      thetaSecondCell_tail_two_eq_two_terms_add_tail_four
        x hx hx1 i j
    _ = thetaAuditedSeriesTerm x i j 2 +
        thetaAuditedSeriesTerm x i j 3 +
        thetaAuditedSeriesTerm x i j 4 +
        thetaAuditedTail 5 x i j := by rw [h45]; ring

/-- Uniform original theta tail n>=2 on the third x-cell fits
the SAME one-percent matrix allowance used for cell 2. -/
theorem thetaThirdCell_tail_two_abs_le_oneHundred
    (x : ℝ) (hax : (177:ℝ)/512 ≤ x)
    (hxb : x ≤ (821:ℝ)/2048) (i j : Fin 5) :
    |thetaAuditedTail 2 x i j| ≤ (1:ℝ)/100 := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num) hax
  have hx1 : x ≤ 1 := by linarith
  obtain ⟨h2,h3,h4⟩ := thetaThirdCell_three_head_abs_bounds x hax hxb
  have h5 := thetaThirdCell_allEntriesTail_five_abs_lt_oneE12 x hx hxb i j
  rw [thetaThirdCell_tail_two_eq_three_terms_add_tail_five x hx hx1 i j]
  have htriangle :
      |thetaAuditedSeriesTerm x i j 2 +
        thetaAuditedSeriesTerm x i j 3 +
        thetaAuditedSeriesTerm x i j 4 +
        thetaAuditedTail 5 x i j| ≤
      |thetaAuditedSeriesTerm x i j 2| +
        |thetaAuditedSeriesTerm x i j 3| +
        |thetaAuditedSeriesTerm x i j 4| +
        |thetaAuditedTail 5 x i j| := by
    calc
      _ ≤ |thetaAuditedSeriesTerm x i j 2 +
            thetaAuditedSeriesTerm x i j 3 +
            thetaAuditedSeriesTerm x i j 4| +
          |thetaAuditedTail 5 x i j| := abs_add_le _ _
      _ ≤ (|thetaAuditedSeriesTerm x i j 2 +
             thetaAuditedSeriesTerm x i j 3| +
          |thetaAuditedSeriesTerm x i j 4|) +
          |thetaAuditedTail 5 x i j| := by
            have h := abs_add_le
              (thetaAuditedSeriesTerm x i j 2 +
                thetaAuditedSeriesTerm x i j 3)
              (thetaAuditedSeriesTerm x i j 4)
            linarith
      _ ≤ _ := by
        have h := abs_add_le
          (thetaAuditedSeriesTerm x i j 2)
          (thetaAuditedSeriesTerm x i j 3)
        linarith
  have hsum :
      (1:ℝ)/200 + 1/(10:ℝ)^9 +
        2/(10:ℝ)^12 < (1:ℝ)/100 := by norm_num
  linarith [htriangle, h2 i j, h3 i j, h4 i j]

/-- UNCONDITIONAL five real pivot signs for the ORIGINAL full theta
matrix on the complete third audited x-cell, assuming no external
numeric theta values or integral accuracy claims. -/
theorem thetaThirdCell_unconditional_allFivePivotSigns
    (x : ℝ) (hax : (177:ℝ)/512 ≤ x)
    (hxb : x ≤ (821:ℝ)/2048) :
    PivotSigns
      (originalThetaRealPivot x 0)
      (originalThetaRealPivot x 1)
      (originalThetaRealPivot x 2)
      (originalThetaRealPivot x 3)
      (originalThetaRealPivot x 4) := by
  exact thetaThirdCell_allFivePivotSigns_of_tail x hax hxb
    (fun i j => thetaThirdCell_tail_two_abs_le_oneHundred
      x hax hxb i j)

end W5
