import W5.ThetaSecondCellPositivePolynomial

/-!
# Reuse the same positive coefficient envelope on every rational cell

The original signed B_ij(d,q), with the true transformed theta
arguments d=(n²-1)/x+w*x and q=n²+w*x², is bounded pointwise
by ONE positive binomial polynomial at rational endpoint
parameters D=(n²-1)/a and b.

This avoids 25 separate coefficient estimates and keeps the
exact original factorial weights, rather than the known but
vastly looser degree-26 all-index majorant.

No integration, analytic tail or numerical certificate is assumed
in these theorems. Their proofs are pointwise real algebra.
-/

namespace W5

/-- Uniform endpoint replacement of the original coefficient
polynomial for EVERY i,j:Fin5, n>=1, w>=0, x∈[a,b]. -/
theorem thetaPositivePolynomial_cell_upper
    (a b x p w : ℝ)
    (ha : 0 < a) (hax : a ≤ x) (hxb : x ≤ b)
    (hp : 1 ≤ p) (hw : 0 ≤ w)
    (i j : Fin 5) :
    |coefficientPolynomial i j ((p-1)/x+w*x) (p+w*x^2)| ≤
      thetaCoefficientPositivePolynomial i j
        ((p-1)/a + w*b) (p+w*b^2) := by
  have hx : 0 < x := ha.trans_le hax
  have hb : 0 < b := hx.trans_le hxb
  have hpm : 0 ≤ p-1 := by linarith
  have hinv : x⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha hax
  have hD :
      (p-1)/x ≤ (p-1)/a := by
    simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hinv hpm
  have hd0 : 0 ≤ (p-1)/x+w*x := by
    apply add_nonneg
    · exact div_nonneg hpm hx.le
    · exact mul_nonneg hw hx.le
  have hd:
      (p-1)/x+w*x ≤ (p-1)/a+w*b := by
    exact add_le_add hD (mul_le_mul_of_nonneg_left hxb hw)
  have hp0 : 0 ≤ p+w*x^2 := by positivity
  have hx_sq : x^2 ≤ b^2 := by
    have hplus : 0 ≤ b+x := by linarith
    have hprod : 0 ≤ (b-x)*(b+x) :=
      mul_nonneg (sub_nonneg.mpr hxb) hplus
    nlinarith
  have hq :
      p+w*x^2 ≤ p+w*b^2 := by
    nlinarith [mul_nonneg hw (sub_nonneg.mpr hx_sq)]
  exact (thetaCoefficientPolynomial_abs_le_positive
    i j _ _ hd0 hp0).trans
    (thetaCoefficientPositivePolynomial_mono
      i j _ _ _ _ hd0 hd hp0 hq)

end W5
