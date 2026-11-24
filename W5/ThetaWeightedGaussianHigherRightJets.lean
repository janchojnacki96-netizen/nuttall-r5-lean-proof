import W5.ThetaGaussianIntegratedSeriesLocalDerivative
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Exact higher right jets of the weighted theta Gaussian

For fixed x,p,d0,u,w, the dependence on v of the weighted
Gaussian is simply an exponential of an affine function. The
v-multiplier is independent of v:
  m = (-d0-p*u) - w*x*(1+x*u).

Consequently EVERY iterated right derivative is m^k times the
original integrand. This proves an exact arbitrary-order *pointwise*
identity without adding analytic interchange assumptions.

IMPORTANT: Differentiating these jets under the unbounded w-integral
and the infinite n-series still requires higher-order integrable,
summable majorants. This module makes no such interchange claim.
-/

namespace W5

/-- The v-derivative multiplier of the transformed weighted theta Gaussian. -/
noncomputable def thetaWeightedGaussianRightMultiplier
    (x p d0 u w : ℝ) : ℝ :=
  (-d0-p*u)-w*x*(1+x*u)

/-- Closed formula for the k-th right jet of the weighted Gaussian. -/
noncomputable def thetaWeightedGaussianRightJet
    (k : ℕ) (x p d0 u v w : ℝ) : ℝ :=
  (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
    thetaWeightedGaussianIntegrand x p d0 u v w

theorem thetaWeightedGaussianRightJet_zero
    (x p d0 u v w : ℝ) :
    thetaWeightedGaussianRightJet 0 x p d0 u v w =
      thetaWeightedGaussianIntegrand x p d0 u v w := by
  simp [thetaWeightedGaussianRightJet]

/-- Each right jet differentiates to the next jet: the multiplier
is constant in the differentiation variable v. -/
theorem thetaWeightedGaussianRightJet_hasDerivAt
    (k : ℕ) (x p d0 u v w : ℝ) :
    HasDerivAt
      (fun z : ℝ => thetaWeightedGaussianRightJet k x p d0 u z w)
      (thetaWeightedGaussianRightJet (k+1) x p d0 u v w) v := by
  let m : ℝ := thetaWeightedGaussianRightMultiplier x p d0 u w
  have h := (thetaWeightedGaussian_hasDerivAt_right
    x p d0 u v w).const_mul (m^k)
  have hmult :
      Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
          (((-d0-p*u)-w*x*(1+x*u)) *
            thetaGaussianModel (d0+w*x) (p+w*x^2) u v) =
        m * thetaWeightedGaussianIntegrand x p d0 u v w := by
    dsimp [m, thetaWeightedGaussianRightMultiplier,
      thetaWeightedGaussianIntegrand]
    ring
  rw [hmult] at h
  have hpow :
      m^k * (m * thetaWeightedGaussianIntegrand x p d0 u v w) =
        thetaWeightedGaussianRightJet (k+1) x p d0 u v w := by
    dsimp [thetaWeightedGaussianRightJet, m]
    rw [pow_succ]
    ring
  rw [hpow] at h
  exact h

/-- The ordinary derivative of the k-th jet is the (k+1)-st jet. -/
theorem thetaWeightedGaussianRightJet_deriv
    (k : ℕ) (x p d0 u v w : ℝ) :
    deriv (fun z : ℝ => thetaWeightedGaussianRightJet k x p d0 u z w) v =
      thetaWeightedGaussianRightJet (k+1) x p d0 u v w :=
  (thetaWeightedGaussianRightJet_hasDerivAt k x p d0 u v w).deriv

/-- Exact formula for arbitrary iterated v-derivatives of the
genuine weighted Gaussian integrand, not just a symbolic jet. -/
theorem thetaWeightedGaussian_iteratedDeriv_right
    (k : ℕ) (x p d0 u v w : ℝ) :
    iteratedDeriv k
        (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w) v =
      thetaWeightedGaussianRightJet k x p d0 u v w := by
  induction k generalizing v with
  | zero =>
      simp [thetaWeightedGaussianRightJet_zero]
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv k
            (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w) =
          (fun z : ℝ => thetaWeightedGaussianRightJet k x p d0 u z w) := by
        funext z
        exact ih z
      rw [hfun]
      exact (thetaWeightedGaussianRightJet_hasDerivAt k x p d0 u v w).deriv

/-- Especially useful for starting a second-order dominated
differentiation argument: the second derivative is the square
of the affine multiplier times the original integrand. -/
theorem thetaWeightedGaussian_second_right_deriv
    (x p d0 u v w : ℝ) :
    iteratedDeriv 2
        (fun z : ℝ => thetaWeightedGaussianIntegrand x p d0 u z w) v =
      (thetaWeightedGaussianRightMultiplier x p d0 u w)^2 *
        thetaWeightedGaussianIntegrand x p d0 u v w := by
  exact thetaWeightedGaussian_iteratedDeriv_right 2 x p d0 u v w

end W5
