import W5.ThetaAllCorrectionSummabilityFubini

/-!
# All 25 original theta corrections as true integrals of convergent sums

The generic original-correction Fubini theorem already proved
in the parent module justifies interchanging the infinite
square-index n-sum and the positive-half-line w-integral
FOR EVERY i,j:Fin5.

We now expose the final unconditional coefficientwise identity
and package it into one exact Fin 5 × Fin 5 matrix theorem:

 thetaCoefficient_ij(x) =
    (∑ n original_base_ij(n)) -
      ∫_{w>0} (∑ n original_correction_integrand_ij(n,w)) dw.

No termwise derivative is needed for this step, and no
matrix sign, normalization bridge or numerical estimate is
introduced by it. We are reusing the existing Mathlib
HasSum.tsum_eq and Matrix.ext machinery rather than proving
each entry's Fubini identity separately.
-/

namespace W5
open MeasureTheory

/-- The n-series of original correction w-integrals and the
single integral of the pointwise n-series agree for every
numerical coefficient, including the n=0 convention. -/
theorem thetaCertificateCorrectionSeries_all_eq_integral_tsum
    (x : ℝ) (i j : Fin 5) (hx : 0 < x) (hx1 : x ≤ 1) :
    (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n) =
      ∫ w : ℝ,
        (∑' n : ℕ, thetaCertificateCorrectionIntegrand x i j n w)
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  calc
    (∑' n : ℕ, thetaCertificateCorrectionTerm x i j n) =
        ∑' n : ℕ,
          (∫ w : ℝ, thetaCertificateCorrectionIntegrand x i j n w
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
      apply tsum_congr
      intro n
      exact thetaCertificateCorrectionTerm_eq_integral x i j n
    _ = _ :=
      (thetaCertificateCorrectionIntegrand_integral_hasSum
        x i j hx hx1).tsum_eq

/-- All ORIGINAL numerical theta coefficients, without a
summability hypothesis, equal the convergent elementary
Gaussian series MINUS the genuine Lebesgue integral of
the absolutely summable correction integrand n-series. -/
theorem thetaCoefficient_all_eq_base_minus_integral_tsum
    (x : ℝ) (i j : Fin 5) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaCoefficient x i j =
      (∑' n : ℕ, thetaCertificateBaseTerm x i j n) -
        (∫ w : ℝ,
          (∑' n : ℕ, thetaCertificateCorrectionIntegrand x i j n w)
            ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  have hsplit :=
    thetaCoefficient_all_eq_base_sub_correction
      x hx i j (thetaCertificateCorrectionTerm_all_summable x hx hx1 i j)
  rw [thetaCertificateCorrectionSeries_all_eq_integral_tsum
    x i j hx hx1] at hsplit
  exact hsplit

/-- Matrix form of the unconditional original theta
certificate decomposition. This is the bridge needed to
compare the 25 numerical coefficients with an independently
derived analytic integral kernel.

The normalized Nuttall kernel equality remains a separate
theorem to prove, and the determinant signs are not assumed. -/
theorem thetaMatrixFive_eq_baseMatrix_minus_integralKernel
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    Matrix.of (fun i j : Fin 5 => thetaCoefficient x i j) =
      Matrix.of (fun i j : Fin 5 =>
        (∑' n : ℕ, thetaCertificateBaseTerm x i j n) -
          (∫ w : ℝ,
            (∑' n : ℕ, thetaCertificateCorrectionIntegrand x i j n w)
              ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
  ext i j
  exact thetaCoefficient_all_eq_base_minus_integral_tsum x i j hx hx1

end W5
