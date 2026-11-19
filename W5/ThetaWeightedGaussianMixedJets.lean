import W5.ThetaGaussianHigherRightJetBound

/-!
# Mixed theta Gaussian jets: one u-derivative after k v-derivatives

The polynomial right-jet multiplier is affine in u, with slope
-(p+w*x²). We differentiate the *actual weighted theta Gaussian*
in the other coordinate and then use the product rule.

This supplies a concrete mixed-jet identity for arbitrary k and,
at the first mixed order, the (d²-q) structure familiar from the
Nuttall/Theta coefficient polynomials. All assertions are pointwise.
Further analytic estimates are needed before commuting these mixed
derivatives with the improper w-integral or the infinite n-series.
-/

namespace W5

/-- The elementary weighted theta Gaussian is symmetric in u and v. -/
theorem thetaWeightedGaussianIntegrand_swap
    (x p d0 u v w : ℝ) :
    thetaWeightedGaussianIntegrand x p d0 u v w =
      thetaWeightedGaussianIntegrand x p d0 v u w := by
  unfold thetaWeightedGaussianIntegrand thetaGaussianModel
  have h :
      -(d0+w*x)*(u+v) - (p+w*x^2)*u*v =
        -(d0+w*x)*(v+u) - (p+w*x^2)*v*u := by ring
  rw [h]

/-- Ordinary left partial derivative of the full weighted theta
integrand; its multiplier is the right multiplier with u and v swapped. -/
theorem thetaWeightedGaussian_hasDerivAt_left
    (x p d0 u v w : ℝ) :
    HasDerivAt
      (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 z v w)
      (thetaWeightedGaussianRightMultiplier x p d0 v w *
        thetaWeightedGaussianIntegrand x p d0 u v w) u := by
  have hfun :
      (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 z v w) =
      (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 v z w) := by
    funext z
    exact thetaWeightedGaussianIntegrand_swap x p d0 z v w
  rw [hfun]
  have h := thetaWeightedGaussian_hasDerivAt_right x p d0 v u w
  have hval :
      Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          (((-d0-p*v)-w*x*(1+x*v)) *
            thetaGaussianModel (d0+w*x) (p+w*x^2) v u) =
        thetaWeightedGaussianRightMultiplier x p d0 v w *
          thetaWeightedGaussianIntegrand x p d0 u v w := by
    rw [thetaWeightedGaussianIntegrand_swap x p d0 u v w]
    dsimp [thetaWeightedGaussianRightMultiplier,
      thetaWeightedGaussianIntegrand]
    ring
  rw [hval] at h
  exact h

/-- The derivative in u of the affine v-jet multiplier is the
negative quadratic Gaussian coefficient. -/
theorem thetaWeightedGaussianRightMultiplier_hasDerivAt_left
    (x p d0 u w : ℝ) :
    HasDerivAt
      (fun z : ℝ => thetaWeightedGaussianRightMultiplier x p d0 z w)
      (-(p+w*x^2)) u := by
  have h := ((hasDerivAt_id u).const_mul (-(p+w*x^2))).const_add (-d0-w*x)
  convert h using 1
  · funext z
    simp only [thetaWeightedGaussianRightMultiplier, id_eq]
    ring
  · ring

/-- Exact u-partial derivative after an arbitrary number k of
v-partial derivatives. This is the first genuinely *mixed* family,
with the cross term -(p+w*x²) appearing explicitly. -/
theorem thetaWeightedGaussianRightJet_hasDerivAt_left
    (k : ℕ) (x p d0 u v w : ℝ) :
    HasDerivAt
      (fun z : ℝ => thetaWeightedGaussianRightJet k x p d0 z v w)
      (((k:ℝ) * (-(p+w*x^2)) *
          (thetaWeightedGaussianRightMultiplier x p d0 u w)^(k-1) +
         (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
          thetaWeightedGaussianRightMultiplier x p d0 v w) *
        thetaWeightedGaussianIntegrand x p d0 u v w) u := by
  have hm := thetaWeightedGaussianRightMultiplier_hasDerivAt_left
    x p d0 u w
  have hf := thetaWeightedGaussian_hasDerivAt_left x p d0 u v w
  have hprod := (hm.pow k).mul hf
  convert hprod using 1
  · funext z
    simp only [thetaWeightedGaussianRightJet]
  · ring

/-- The first mixed derivative has the exact quadratic expression
multiplier_u * multiplier_v - (p+w*x²). -/
theorem thetaWeightedGaussian_mixed_one_one
    (x p d0 u v w : ℝ) :
    deriv (fun z : ℝ =>
      thetaWeightedGaussianRightJet 1 x p d0 z v w) u =
      ((thetaWeightedGaussianRightMultiplier x p d0 u w *
        thetaWeightedGaussianRightMultiplier x p d0 v w) -
          (p+w*x^2)) *
        thetaWeightedGaussianIntegrand x p d0 u v w := by
  rw [(thetaWeightedGaussianRightJet_hasDerivAt_left
    1 x p d0 u v w).deriv]
  simp only [Nat.cast_one, pow_zero, pow_one, mul_one, one_mul]
  ring

/-- At u=v=0, the mixed coefficient is exactly (d²-q)
with d=d0+w*x and q=p+w*x², as used in the low-order theta
coefficient polynomials. -/
theorem thetaWeightedGaussian_mixed_one_one_zero
    (x p d0 w : ℝ) :
    deriv (fun z : ℝ =>
      thetaWeightedGaussianRightJet 1 x p d0 z 0 w) 0 =
      ((d0+w*x)^2-(p+w*x^2)) *
        thetaWeightedGaussianIntegrand x p d0 0 0 w := by
  rw [thetaWeightedGaussian_mixed_one_one]
  simp only [thetaWeightedGaussianRightMultiplier, mul_zero,
    zero_mul, add_zero, one_add, mul_one, sub_zero]
  ring

end W5
