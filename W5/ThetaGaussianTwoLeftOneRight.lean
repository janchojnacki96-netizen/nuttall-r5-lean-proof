import W5.ThetaMixedRightJetSeriesDerivative

/-!
# A genuine (2,1) mixed theta Gaussian derivative

The order-(1,1) mixed derivative of the full weighted Gaussian was
already proved pointwise. This module differentiates it once more in
the left Taylor coordinate. At the Taylor origin the resulting
polynomial is -d^3+2*d*q, i.e. twice the expected (2,1) Taylor
coefficient of exp(-d(u+v)-q*u*v).

This is a real calculus theorem for the actual Gaussian integrand.
It does not interchange this derivative with an improper integral
or infinite theta series, nor prove a Nuttall determinant sign.
-/

namespace W5

/-- Genuine two-left/one-right ordinary mixed derivative of the
weighted Gaussian, including the q=p+w*x² cross term. -/
theorem thetaWeightedGaussian_two_left_one_right
    (x p d0 u v w : ℝ) :
    deriv
      (fun z : ℝ =>
        deriv (fun y : ℝ =>
          thetaWeightedGaussianRightJet 1 x p d0 y v w) z) u =
      ((thetaWeightedGaussianRightMultiplier x p d0 u w *
          (thetaWeightedGaussianRightMultiplier x p d0 v w)^2 -
        2*(p+w*x^2) *
          thetaWeightedGaussianRightMultiplier x p d0 v w) *
        thetaWeightedGaussianIntegrand x p d0 u v w) := by
  let M : ℝ → ℝ := fun z =>
    thetaWeightedGaussianRightMultiplier x p d0 z w
  let L : ℝ := thetaWeightedGaussianRightMultiplier x p d0 v w
  let Q : ℝ := p+w*x^2
  let G : ℝ → ℝ := fun z =>
    thetaWeightedGaussianIntegrand x p d0 z v w
  have hm : HasDerivAt M (-Q) u := by
    exact thetaWeightedGaussianRightMultiplier_hasDerivAt_left
      x p d0 u w
  have hp0 := (hm.mul_const L).add_const (-Q)
  have hp : HasDerivAt (fun z : ℝ => M z * L - Q)
      (-Q*L) u := by
    convert hp0 using 1
    · funext z
      ring
    · ring
  have hg : HasDerivAt G (L*G u) u := by
    exact thetaWeightedGaussian_hasDerivAt_left x p d0 u v w
  have hprod := hp.mul hg
  have hvalue :
      deriv (fun z : ℝ => (M z*L-Q)*G z) u =
        ((M u*L^2-2*Q*L)*G u) := by
    convert hprod.deriv using 1
    ring
  have hfun :
      (fun z : ℝ =>
        deriv (fun y : ℝ =>
          thetaWeightedGaussianRightJet 1 x p d0 y v w) z) =
      (fun z : ℝ => (M z*L-Q)*G z) := by
    funext z
    simpa only [M, L, Q, G] using
      (thetaWeightedGaussian_mixed_one_one x p d0 z v w)
  rw [hfun]
  exact hvalue

/-- At the Taylor origin, the (2,1) derivative polynomial is
-d^3+2*d*q for d=d0+w*x and q=p+w*x². -/
theorem thetaWeightedGaussian_two_left_one_right_zero
    (x p d0 w : ℝ) :
    deriv (fun z : ℝ =>
      deriv (fun y : ℝ =>
        thetaWeightedGaussianRightJet 1 x p d0 y 0 w) z) 0 =
      (-(d0+w*x)^3 + 2*(p+w*x^2)*(d0+w*x)) *
        thetaWeightedGaussianIntegrand x p d0 0 0 w := by
  rw [thetaWeightedGaussian_two_left_one_right]
  dsimp [thetaWeightedGaussianRightMultiplier]
  ring

end W5
