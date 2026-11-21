import W5.CoefficientTailBound
import W5.ThetaCertificateBaseCorrectionSplit
import W5.ThetaAuditedMajorantUniformParameter

/-!
# Original theta BASE terms obey the independently audited tail majorant

Unlike the numerical LDL sign checks or the 51-entry conditional
enclosure chain, this lemma proves a genuine, uniform inequality for
the ORIGINAL coefficient's elementary square-index term.
It reuses the existing `coefficientPolynomial_abs_bound`
for all 25 entries, without reproducing any polynomial audit.

For 0<x<=1 and n>=2, putting p=n² and y=1/x²:

  |base_{ij}(x,n)|
    <= 5*4096 * y⁴ * n²⁶ * exp(-(n²-1)*y).

The constant 4096 is exactly 2^12, coming from the
(1+d)^8*(1+q)^4 polynomial bound. This is the BASE component
of the original integer auditor's much larger
5*4096*30000000000 majorant.

The integral correction still requires a quantitative weighted-
Gaussian moment bound and is NOT claimed to be controlled here.
-/

namespace W5

/-- The already certified polynomial bound combined with the
actual theta arguments d=(p-1)/x and q=p. -/
theorem thetaCoefficientPolynomial_at_base_abs_le
    (x p : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (hp : 1 ≤ p) (i j : Fin 5) :
    |coefficientPolynomial i j ((p-1)/x) p| ≤
      (5*4096 : ℝ) * p^12 * (1/x^2)^4 := by
  let d : ℝ := (p-1)/x
  have hd : 0 ≤ d := by
    dsimp [d]
    exact div_nonneg (by linarith) hx.le
  have hp0 : 0 ≤ p := by linarith
  have hD : 1+d ≤ 2*p/x := by
    dsimp [d]
    apply (le_div_iff₀ hx).mpr
    have h : (p-1)/x*x = p-1 :=
      div_mul_cancel₀ _ (ne_of_gt hx)
    nlinarith
  have hQ : 1+p ≤ 2*p := by linarith
  have h8 : (1+d)^8 ≤ (2*p/x)^8 :=
    pow_le_pow_left₀ (by positivity) hD 8
  have h4 : (1+p)^4 ≤ (2*p)^4 :=
    pow_le_pow_left₀ (by positivity) hQ 4
  calc
    |coefficientPolynomial i j ((p-1)/x) p| ≤
        (5:ℝ)*(1+d)^8*(1+p)^4 := by
      simpa only [d] using coefficientPolynomial_abs_bound
        i j ((p-1)/x) p (div_nonneg (by linarith) hx.le) hp0
    _ ≤ (5:ℝ)*(2*p/x)^8*(1+p)^4 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left h8 (by norm_num))
        (by positivity)
    _ ≤ (5:ℝ)*(2*p/x)^8*(2*p)^4 :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = (5*4096:ℝ)*p^12*(1/x^2)^4 := by
      field_simp [ne_of_gt hx]
      ring

/-- Every original theta elementary base summand (n>=2)
has the exact exponent-26 integer-audit majorant, uniformly
over all i,j:Fin5, with no unproved analytic hypothesis. -/
theorem thetaCertificateBaseTerm_abs_le_audited_majorant
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 5) (n : ℕ) (hn : 2 ≤ n) :
    |thetaCertificateBaseTerm x i j n| ≤
      (5*4096:ℝ)*(1/x^2)^4 *
        thetaMajorantTerm (1/x^2) n := by
  have hnonzero : n ≠ 0 := by omega
  let p : ℝ := (n:ℝ)^2
  let d : ℝ := (p-1)/x
  let E : ℝ := Real.exp (-(p-1)/x^2)
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : 1 ≤ p := by
    dsimp [p]
    nlinarith [sq_nonneg ((n:ℝ)-2)]
  have hp0 : 0 ≤ p := by linarith
  have hE : 0 ≤ E := Real.exp_nonneg _
  have hpoly :
      |coefficientPolynomial i j d p| ≤
        (5*4096:ℝ)*p^12*(1/x^2)^4 := by
    simpa only [d] using
      thetaCoefficientPolynomial_at_base_abs_le x p hx hx1 hp i j
  have hbase :
      |thetaCertificateBaseTerm x i j n| =
        p*E*|coefficientPolynomial i j d p| := by
    simp only [thetaCertificateBaseTerm, if_neg hnonzero]
    change |p*E*coefficientPolynomial i j d p| =
      p*E*|coefficientPolynomial i j d p|
    rw [abs_mul, abs_mul, abs_of_nonneg hp0, abs_of_nonneg hE]
  calc
    |thetaCertificateBaseTerm x i j n| =
        p*E*|coefficientPolynomial i j d p| := hbase
    _ ≤ p*E*((5*4096:ℝ)*p^12*(1/x^2)^4) :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg hp0 hE)
    _ = (5*4096:ℝ)*(1/x^2)^4 *
          thetaMajorantTerm (1/x^2) n := by
      dsimp [p, E, thetaMajorantTerm]
      ring

end W5
