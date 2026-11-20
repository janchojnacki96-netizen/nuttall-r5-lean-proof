import W5.ThetaMixedJetIntegralAndSeriesDerivative
import W5.ThetaMixedRightJetSeriesDerivative

/-!
# Exact B11 polynomial in the GENUINE mixed derivative of the theta integral series

The previous all-orders mixed differentiation theorem permits the
left derivative of the first right derivative of the actual
transformed Gaussian theta series to cross both the genuine Lebesgue
w-integral and the infinite square-index n-sum.

We now replace the resulting pointwise Gaussian mixed jet with the
EXACT B11(d,q)=d²-q polynomial of the independent numerical
certificate, *inside* the genuine infinite sum and integral.

The second theorem uses the already verified Fubini identity to
put the integral inside the n-sum. Neither theorem assumes a
formal coefficient identity, and neither claims the still-missing
identification with normalizedKernel or a determinant sign.
-/

namespace W5

open MeasureTheory

/-- For x>0 the origin lies in the common Gaussian differentiability
patch used by the all-orders differentiated infinite series. -/
theorem thetaGaussianSummableRightPatch_origin
    (x : ℝ) (hx : 0 < x) :
    (0:ℝ) ∈ thetaGaussianSummableRightPatch x :=
  thetaGaussianSummableRightPatch_zero_mem x hx

/-- The actual mixed (1,1) derivative of the full transformed
Gaussian theta series equals one REAL integral of the infinite
series of the numerical certificate polynomial B11(d,q). -/
theorem thetaGaussianIntegratedSeries_mixed_one_one_eq_B11_integral_tsum
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv
      (fun z : ℝ =>
        iteratedDeriv 1
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 =
      ∫ w : ℝ,
        (∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (1:Fin 5)
                  (d0+w*x) (p+w*x^2)))
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz := thetaGaussianSummableRightPatch_origin x hx
  have h := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    1 x 0 0 hx hx1 hz hz
  have hfun :
      (fun w : ℝ =>
        ∑' n : ℕ, thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w) =
      (fun w : ℝ =>
        ∑' n : ℕ,
          if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (1:Fin 5)
                  (d0+w*x) (p+w*x^2))) := by
    funext w
    apply tsum_congr
    intro n
    exact thetaMixedOneRightJetSeriesTerm_one_zero x n w
  rw [hfun] at h
  exact h

/-- The same actual mixed derivative, now in the exact form of a
square-index series of genuine Lebesgue integrals of B11(d,q).
Both the differentiation and Fubini operations were justified in
earlier Lean theorems; no postulated exchanges are used. -/
theorem thetaGaussianIntegratedSeries_mixed_one_one_eq_B11_tsum_integral
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    deriv
      (fun z : ℝ =>
        iteratedDeriv 1
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 =
      ∑' n : ℕ,
        ∫ w : ℝ,
          (if n = 0 then (0:ℝ) else
            let p : ℝ := (n:ℝ)^2
            let d0 : ℝ := (p-1)/x
            Real.exp (-(p-1)/x^2) *
              (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                coefficientPolynomial (1:Fin 5) (1:Fin 5)
                  (d0+w*x) (p+w*x^2)))
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := by
  have hz := thetaGaussianSummableRightPatch_origin x hx
  have hbase := thetaGaussianIntegratedSeries_deriv_left_iteratedDeriv_right_eq
    1 x 0 0 hx hx1 hz hz
  have hzero : |(0:ℝ)| ≤ x/8 := by
    simp only [abs_zero]
    positivity
  have hFubini := thetaMixedOneRightJetSeries_integral_hasSum
    1 x 0 0 hx hx1 hzero hzero
  calc
    deriv
        (fun z : ℝ =>
          iteratedDeriv 1
            (fun y : ℝ =>
              ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0 =
      ∫ w : ℝ, ∑' n : ℕ,
        thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))) := hbase
    _ = ∑' n : ℕ,
      ∫ w : ℝ, thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w
        ∂(volume.restrict (Set.Ioi (0:ℝ))) := hFubini.tsum_eq.symm
    _ = _ := by
      apply tsum_congr
      intro n
      have hterm := thetaMixedOneRightJetSeriesTerm_one_zero x n
      have hfunc :
          (fun w : ℝ => thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w) =
          (fun w : ℝ =>
            if n = 0 then (0:ℝ) else
              let p : ℝ := (n:ℝ)^2
              let d0 : ℝ := (p-1)/x
              Real.exp (-(p-1)/x^2) *
                (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
                  coefficientPolynomial (1:Fin 5) (1:Fin 5)
                    (d0+w*x) (p+w*x^2))) := by
        funext w
        exact hterm w
      rw [hfunc]

end W5
