import W5.ThetaSecondCellOneSquareZeroZeroRealWitness
import W5.ThetaAllSquareIndexNineMoments

/-!
# Sharp genuine theta square-index terms for entry (0,0)

The existing twenty-five-entry polynomial majorant scales as n^26,
which is much too wide for the small second-cell interval margin.

For the actual original (0,0) coefficient, B₀₀(d,q) = 1 for
*all* d,q. Hence the original n-th base term carries n² and the
integral correction is exactly the zeroth weighted Gamma moment.
This is an identity of the TRUE theta series, not a surrogate.

Reuse the already verified Mathlib-integral Gamma upper/lower bounds,
including the n=1 moment lemmas; no integrals are re-proved here.
-/

namespace W5

/-- Uniform exact constant polynomial for entry (0,0), now
independent of square index n and of both affine parameters. -/
theorem thetaCorrectionWPolynomial_zero_zero_all
    (x p d : ℝ) :
    thetaCorrectionWPolynomial x p d (0 : Fin 5) (0 : Fin 5) =
      Polynomial.C 1 := by
  simp [thetaCorrectionWPolynomial]

/-- Every nonzero original square-index BASE term for entry (0,0)
has the full n² prefactor; at n=1 this specializes to 1. -/
theorem thetaCertificateBaseTerm_zero_zero_eq
    (x : ℝ) (n : ℕ) (hn : 0 < n) :
    thetaCertificateBaseTerm x (0 : Fin 5) (0 : Fin 5) n =
      ((n : ℝ)^2) * Real.exp (-((n : ℝ)^2-1)/x^2) := by
  simp [thetaCertificateBaseTerm, Nat.ne_of_gt hn,
    coefficientPolynomial_zero_zero]

/-- Original n-th theta series coefficient, NOT just a numerical
bound or an abstract interval: one Gaussian and a genuine
Lebesgue weighted moment M₀(x/n). -/
theorem thetaAuditedSeriesTerm_zero_zero_eq_gaussian_moment
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) n =
      Real.exp (-((n : ℝ)^2-1)/x^2) *
        ((n : ℝ)^2 -
          (x^2/4) * thetaAuditedOneWeightedMoment (x/(n:ℝ)) 0) := by
  have hsum :
      (∑ k ∈ Finset.range 9,
        (thetaCorrectionWPolynomial
          x ((n:ℝ)^2) (((n:ℝ)^2-1)/x)
            (0 : Fin 5) (0 : Fin 5)).coeff k *
          thetaAuditedOneWeightedMoment (x/(n:ℝ)) k) =
        thetaAuditedOneWeightedMoment (x/(n:ℝ)) 0 := by
    simp [thetaCorrectionWPolynomial_zero_zero_all,
      Polynomial.coeff_one, Polynomial.coeff_C,
      Finset.sum_range_succ]
  calc
    thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) n =
        thetaCertificateBaseTerm x (0 : Fin 5) (0 : Fin 5) n -
          (x^2/4) * Real.exp (-((n:ℝ)^2-1)/x^2) *
            thetaAuditedOneWeightedMoment (x/(n:ℝ)) 0 := by
              simpa only [hsum] using
                (thetaAuditedSeriesTerm_nine_moments x hx hx1
                  (0 : Fin 5) (0 : Fin 5) n hn)
    _ = _ := by
      rw [thetaCertificateBaseTerm_zero_zero_eq x n hn]
      ring

/-- The true n-th term for B₀₀ is nonnegative and bounded by
its elementary Gaussian base. Unlike the general n^26 majorant,
the upper bound only contains n² and applies to EVERY n>0. -/
theorem thetaAuditedSeriesTerm_zero_zero_nonneg_le_gaussian
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 0 < n) :
    0 ≤ thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) n ∧
      thetaAuditedSeriesTerm x (0 : Fin 5) (0 : Fin 5) n ≤
        ((n : ℝ)^2) * Real.exp (-((n : ℝ)^2-1)/x^2) := by
  have hn1 : 1 ≤ n := by omega
  have hnRpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnR1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  let y : ℝ := x/(n:ℝ)
  let M : ℝ := thetaAuditedOneWeightedMoment y 0
  have hy0 : 0 ≤ y := div_nonneg hx.le hnRpos.le
  have hy1 : y ≤ 1 := (div_le_iff₀ hnRpos).2 (by linarith)
  have hMlo : (1 : ℝ) ≤ M := by
    simpa only [Nat.factorial_zero, Nat.cast_one] using
      (thetaAuditedOneWeightedMoment_gamma_lower y hy0 hy1 0)
  have hMup : M ≤ 5/4 := by
    have hupper := thetaAuditedOneWeightedMoment_gamma_upper_quarter
      y hy0 hy1 0
    have hysq : y^2 ≤ 1 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hy1)
        (add_nonneg hy0 (by norm_num : (0:ℝ) ≤ 1))]
    norm_num at hupper
    nlinarith
  have hxsq : x^2 ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx1)
      (add_nonneg hx.le (by norm_num : (0:ℝ) ≤ 1))]
  have hxcorr_nonneg : 0 ≤ (x^2/4)*M :=
    mul_nonneg (by positivity) (by linarith)
  have hxcorr_upper : (x^2/4)*M ≤ 5/16 := by
    have hfactor : x^2/4 ≤ (1/4 : ℝ) := by linarith
    calc
      _ ≤ (1/4 : ℝ) * M :=
        mul_le_mul_of_nonneg_right hfactor (by linarith)
      _ ≤ (1/4 : ℝ) * (5/4 : ℝ) :=
        mul_le_mul_of_nonneg_left hMup (by norm_num)
      _ = 5/16 := by norm_num
  have hn2 : (1 : ℝ) ≤ (n : ℝ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hnR1)
      (add_nonneg (by linarith : (0:ℝ) ≤ (n:ℝ))
        (by norm_num : (0:ℝ) ≤ 1))]
  have hbracket0 :
      0 ≤ (n : ℝ)^2 - (x^2/4)*M := by linarith
  have hbracketHi :
      (n : ℝ)^2 - (x^2/4)*M ≤ (n : ℝ)^2 := by linarith
  rw [thetaAuditedSeriesTerm_zero_zero_eq_gaussian_moment
    x hx hx1 n hn]
  dsimp [M, y] at hbracket0 hbracketHi
  constructor
  · exact mul_nonneg (Real.exp_nonneg _) hbracket0
  · exact mul_le_mul_of_nonneg_left hbracketHi (Real.exp_nonneg _)

end W5
