import W5.ThetaOriginalGammaBracketCertificateBridge

/-!
# Entire ORIGINAL Nuttall normalized kernel = exact certificate Gaussian series

The original normalizedKernel was reduced to its TRUE infinite
gamma square-index series in #109. The verified single-square change
of variables and pointwise Gaussian bracket formula were developed
in #110-#112 using existing Mathlib integral theorems.

We now apply `tsum_congr`: each n-th original gamma summand is
EXACTLY the corresponding transformed certificate Gaussian summand.
This proves a genuine TWO-VARIABLE FUNCTION identity on the original
positive local Taylor patch. It is not a formal Taylor approximation,
a numerical surrogate, or a declaration of `thetaTransformCorrect`.

The remaining step to identify all 25 numerical thetaCoefficient
values with analyticCoeff is to justify extraction of the mixed
Taylor jets (orders 0..4 in each variable) through the infinite
sum and improper w-integral. The prior local Mathlib derivative
infrastructure addresses parts of that obligation.
-/

namespace W5
open MeasureTheory

/-- The actual original Gaussian CERTIFICATE series term, for
arbitrary u,v, prior to taking mixed derivatives. Exactly the
same p, d0, q and x²/(4p) correction as in thetaCoefficient. -/
noncomputable def thetaCertificateGaussianFullTerm
    (x u v : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else
    let p : ℝ := (n:ℝ)^2
    let d0 : ℝ := (p-1)/x
    p * Real.exp (-(p-1)/x^2) *
      (thetaGaussianModel d0 p u v -
        (x^2/(4*p)) *
          (∫ w in Set.Ioi (0:ℝ),
            Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
              thetaGaussianModel (d0+w*x) (p+w*x^2) u v))

/-- Equality of the ENTIRE original normalizedKernel and the
true transformed certificate Gaussian function, on the
original verified local two-parameter patch. In particular,
no analytic interchange is needed to establish the function
identity itself, since equality is proved term by term. -/
theorem normalizedKernel_eq_thetaCertificateGaussianFullSeries
    (x u v : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256)
    (hu : |u| ≤ x/8) (hv : |v| ≤ x/8) :
    normalizedKernel x u v =
      ∑' n : ℕ, thetaCertificateGaussianFullTerm x u v n := by
  rw [normalizedKernel_eq_actual_gamma_square_series
    x u v hx hxB hu hv]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateGaussianFullTerm]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hp : 0 < (n:ℝ)^2 := by
      have hnR : 0 < (n:ℝ) := by exact_mod_cast hnpos
      positivity
    have h :=
      theta_original_gamma_bracket_eq_certificate
        x ((n:ℝ)^2) u v hx hp
    simpa only [thetaCertificateGaussianFullTerm, if_neg hn, mul_assoc]
      using congrArg (fun z : ℝ => (n:ℝ)^2 * z) h

end W5
