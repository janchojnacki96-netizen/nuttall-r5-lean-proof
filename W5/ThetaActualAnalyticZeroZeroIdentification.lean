import W5.ThetaActualNormalizedKernelCertificateSeries
import W5.ThetaCertificateBaseCorrectionSplit

/-!
# First fully identified analytic/numerical theta coefficient: (0,0)

The new exact function identity equating the ORIGINAL normalized
Nuttall kernel with the full Gaussian certificate series is combined
with the earlier verified (0,0) elementary Gaussian and polynomial
identities. At u=v=0, no derivative/sum interchange is necessary:
the 0th derivatives are just function evaluation.

The true (0,0) analytic coefficient therefore equals the
independently defined thetaCoefficient, without assuming
thetaTransformCorrect, any numerical interval enclosure, or a
Wronskian sign. This settles ONE of the 25 entries needed by the
full 5×5 analytic identification.
-/

namespace W5
open MeasureTheory

/-- The Gaussian certificate's zeroth-order summand equals the
already verified base-minus-correction coefficient summand.
The exact cancellation of p in the correction was previously
proved in `thetaCoefficient_cancel_square_index`. -/
theorem thetaCertificateGaussianFullTerm_at_origin
    (x : ℝ) (n : ℕ) :
    thetaCertificateGaussianFullTerm x 0 0 n =
      thetaCertificateBaseTerm x (0:Fin 5) (0:Fin 5) n -
        thetaCertificateCorrectionTerm x (0:Fin 5) (0:Fin 5) n := by
  by_cases hn : n = 0
  · subst n
    simp [thetaCertificateGaussianFullTerm,
      thetaCertificateBaseTerm, thetaCertificateCorrectionTerm]
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hnpos
    have hp : ((n:ℝ)^2) ≠ 0 := by positivity
    simp only [thetaCertificateGaussianFullTerm,
      thetaCertificateBaseTerm, thetaCertificateCorrectionTerm,
      if_neg hn, thetaGaussianModel_zero_zero,
      coefficientPolynomial_zero_zero,
      MeasureTheory.integral_Ici_eq_integral_Ioi, mul_one]
    simpa only [mul_one] using
      (thetaCoefficient_cancel_square_index x ((n:ℝ)^2)
        (Real.exp (-((n:ℝ)^2-1)/x^2)) 1
        (∫ w in Set.Ioi (0:ℝ),
          Real.exp (-w) *
            (1+w*x^2/((n:ℝ)^2))^((1:ℝ)/4)) hp)

/-- Actual original normalizedKernel at (u,v)=(0,0) equals
the original independent theta certificate coefficient B00.
There are no differentiation or infinite-sum exchanges here,
just already proven termwise equality of absolutely-defined sums. -/
theorem normalizedKernel_at_origin_eq_thetaCoefficient
    (x : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256) :
    normalizedKernel x 0 0 =
      thetaCoefficient x (0:Fin 5) (0:Fin 5) := by
  have hz : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  rw [normalizedKernel_eq_thetaCertificateGaussianFullSeries
    x 0 0 hx hxB hz hz]
  rw [thetaCoefficient_eq_tsum_base_sub_correction]
  apply tsum_congr
  intro n
  exact thetaCertificateGaussianFullTerm_at_origin x n

/-- The ORIGINAL analytically differentiated coefficient A00
is just the value of the genuine normalized kernel at the origin. -/
theorem analyticCoeff_zero_zero_eq_normalizedKernel (x : ℝ) :
    analyticCoeff x (0:Fin 5) (0:Fin 5) =
      normalizedKernel x 0 0 := by
  simp [analyticCoeff, iteratedDeriv_zero]

/-- UNCONDITIONAL identification of the (0,0) entry of the true
analytic theta matrix with the independent numerical coefficient.
The only input is the original positive x-range, not a statement
about any determinant sign or other 24 coefficient identities. -/
theorem analyticCoeff_zero_zero_eq_thetaCoefficient
    (x : ℝ) (hx : 0 < x)
    (hxB : x ≤ (145:ℝ)/256) :
    analyticCoeff x (0:Fin 5) (0:Fin 5) =
      thetaCoefficient x (0:Fin 5) (0:Fin 5) := by
  rw [analyticCoeff_zero_zero_eq_normalizedKernel]
  exact normalizedKernel_at_origin_eq_thetaCoefficient x hx hxB

end W5
