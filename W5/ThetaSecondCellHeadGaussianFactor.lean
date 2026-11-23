import W5.ThetaSecondCellHeadFiniteMajorants

/-!
# Reusable Gaussian exponent and finite rational head-cap transport

The certified second-cell head majorants require the same exponent
monotonicity argument for n=2 and n=3 on both subcells. Use ONE
general lemma in the positive reals, then cast already checked
rational K caps. The only remaining analytic premise in the final
head-term inequality is actual real domination by K.
-/

namespace W5

/-- For 0<x<=b, the original Gaussian factor is uniformly
bounded by exp(-E) whenever E*b²<=n²-1. -/
theorem thetaHeadGaussian_le_exp_of_cell
    (n : ℕ) (x b E : ℝ)
    (hx : 0 < x) (hxb : x ≤ b)
    (hE : 0 ≤ E)
    (hcap : E*b^2 ≤ (n:ℝ)^2-1) :
    Real.exp (-((n:ℝ)^2-1)/x^2) ≤ Real.exp (-E) := by
  have hb : 0 < b := hx.trans_le hxb
  have hprod : 0 ≤ (b-x)*(b+x) :=
    mul_nonneg (by linarith) (by linarith)
  have hsq : x^2 ≤ b^2 := by nlinarith [hprod]
  have hnum : E*x^2 ≤ (n:ℝ)^2-1 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq hE]
  have hrec : E ≤ ((n:ℝ)^2-1)/x^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).2 hnum
  apply Real.exp_le_exp.mpr
  simpa only [neg_div] using (neg_le_neg hrec)

/-- Once a common real-sound K bound is supplied, its exact
rational check plus the Gaussian endpoint inequality transports
it to an unconditional real numerical bound on the TRUE term. -/
theorem thetaHeadTerm_abs_le_of_rational_majorant
    (a b C : ℚ) (n : ℕ) (x E δ : ℝ)
    (i j : Fin 5)
    (hx : 0 < x) (hxb : x ≤ (b : ℝ))
    (hE : 0 ≤ E)
    (hEcap : E*(b:ℝ)^2 ≤ (n:ℝ)^2-1)
    (hC : 0 ≤ (C : ℝ))
    (hRational : thetaHeadPositiveMajorant a b n i j ≤ C)
    (hReal : |thetaAuditedSeriesTerm x i j n| ≤
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        (thetaHeadPositiveMajorant a b n i j : ℝ))
    (hExp : Real.exp (-E) ≤ δ) :
    |thetaAuditedSeriesTerm x i j n| ≤ (C:ℝ)*δ := by
  have hBound : (thetaHeadPositiveMajorant a b n i j : ℝ) ≤ (C:ℝ) := by
    exact_mod_cast hRational
  calc
    |thetaAuditedSeriesTerm x i j n| ≤
      Real.exp (-((n:ℝ)^2-1)/x^2) *
        (thetaHeadPositiveMajorant a b n i j : ℝ) := hReal
    _ ≤ Real.exp (-((n:ℝ)^2-1)/x^2)*(C:ℝ) :=
      mul_le_mul_of_nonneg_left hBound (Real.exp_nonneg _)
    _ ≤ Real.exp (-E)*(C:ℝ) :=
      mul_le_mul_of_nonneg_right
        (thetaHeadGaussian_le_exp_of_cell n x (b:ℝ) E hx hxb hE hEcap) hC
    _ ≤ δ*(C:ℝ) := mul_le_mul_of_nonneg_right hExp hC
    _ = (C:ℝ)*δ := by ring

end W5
