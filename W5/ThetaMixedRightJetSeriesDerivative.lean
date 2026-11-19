import W5.ThetaAllOrdersLeftSeriesSymmetry
import W5.ThetaGaussianModelLowOrder

/-!
# A genuine mixed derivative for every theta square-index right jet

All-order differentiation of the full transformed theta series in one
Taylor variable was established in PRs #51-#53. The next analytical
obligation is differentiation of these higher right jets in the *left*
variable, with estimates sufficiently strong to exchange that mixed
derivative with the w-integral and the n-series.

Here we establish the exact pointwise derivative for EVERY fixed right
order k, including the zero square-index convention. At k=1 and
u=v=0 it is precisely the (d²-q) polynomial defining the numerical
certificate's B11 coefficient, multiplied by the genuine weight.

These are unconditional pointwise identities, not derivative/integral
or derivative/tsum interchange theorems and not a W5 sign proof.
-/

namespace W5

/-- The exact mixed (one left, k right) jet of an individual
weighted, damped, square-index Gaussian. The k=0 convention uses
natural-number subtraction, so the leading term vanishes. -/
noncomputable def thetaMixedOneRightJetSeriesTerm
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) : ℝ :=
  if n = 0 then 0 else
    let p : ℝ := (n : ℝ)^2
    let d0 : ℝ := (p-1)/x
    Real.exp (-(p-1)/x^2) *
      (((k:ℝ) * (-(p+w*x^2)) *
          (thetaWeightedGaussianRightMultiplier x p d0 u w)^(k-1) +
        (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
          thetaWeightedGaussianRightMultiplier x p d0 v w) *
        thetaWeightedGaussianIntegrand x p d0 u v w)

/-- The k-th *right* jet has the claimed genuine derivative in the
*left* coordinate, before any integral or series interchange. -/
theorem thetaHigherRightJetSeriesTerm_hasDerivAt_left
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) :
    HasDerivAt
      (fun z : ℝ => thetaHigherRightJetSeriesTerm k x z v n w)
      (thetaMixedOneRightJetSeriesTerm k x u v n w) u := by
  by_cases hn : n = 0
  · subst n
    change HasDerivAt (fun _ : ℝ => (0:ℝ)) (0:ℝ) u
    exact hasDerivAt_const u 0
  · let p : ℝ := (n:ℝ)^2
    let d0 : ℝ := (p-1)/x
    have h := (thetaWeightedGaussianRightJet_hasDerivAt_left
      k x p d0 u v w).const_mul (Real.exp (-(p-1)/x^2))
    change HasDerivAt
      (fun z : ℝ =>
        if n = 0 then (0:ℝ) else
          Real.exp (-(p-1)/x^2) *
            thetaWeightedGaussianRightJet k x p d0 z v w)
      (if n = 0 then (0:ℝ) else
        Real.exp (-(p-1)/x^2) *
          (((k:ℝ) * (-(p+w*x^2)) *
              (thetaWeightedGaussianRightMultiplier x p d0 u w)^(k-1) +
            (thetaWeightedGaussianRightMultiplier x p d0 u w)^k *
              thetaWeightedGaussianRightMultiplier x p d0 v w) *
            thetaWeightedGaussianIntegrand x p d0 u v w)) u
    simpa only [if_neg hn] using h

/-- An exact formula for the ordinary left derivative of
the kth right jet, for every square index. -/
theorem thetaHigherRightJetSeriesTerm_deriv_left
    (k : ℕ) (x u v : ℝ) (n : ℕ) (w : ℝ) :
    deriv (fun z : ℝ => thetaHigherRightJetSeriesTerm k x z v n w) u =
      thetaMixedOneRightJetSeriesTerm k x u v n w :=
  (thetaHigherRightJetSeriesTerm_hasDerivAt_left k x u v n w).deriv

/-- The zeroth right jet has exactly the first left derivative
expected from Gaussian symmetry, for all indices including zero. -/
theorem thetaMixedOneRightJetSeriesTerm_zero
    (x u v : ℝ) (n : ℕ) (w : ℝ) :
    thetaMixedOneRightJetSeriesTerm 0 x u v n w =
      thetaHigherLeftJetSeriesTerm 1 x u v n w := by
  by_cases hn : n = 0
  · simp [thetaMixedOneRightJetSeriesTerm,
      thetaHigherLeftJetSeriesTerm, thetaHigherRightJetSeriesTerm, hn]
  · simp only [thetaMixedOneRightJetSeriesTerm,
      thetaHigherLeftJetSeriesTerm, thetaHigherRightJetSeriesTerm,
      if_neg hn]
    simp only [Nat.cast_zero, zero_mul, zero_add, pow_zero, one_mul]
    rfl

/-- In the original theta coordinates, the mixed (1,1) square-index
jet at the origin is exactly B11(d,q) with the real integral weight.
This is the polynomial appearing in the certificate's 1,1 entry. -/
theorem thetaMixedOneRightJetSeriesTerm_one_zero
    (x : ℝ) (n : ℕ) (w : ℝ) :
    thetaMixedOneRightJetSeriesTerm 1 x 0 0 n w =
      if n = 0 then 0 else
        let p : ℝ := (n : ℝ)^2
        let d0 : ℝ := (p-1)/x
        Real.exp (-(p-1)/x^2) *
          (Real.exp (-w) * (1+w*x^2/p)^((1:ℝ)/4) *
            coefficientPolynomial (1:Fin 5) (1:Fin 5)
              (d0+w*x) (p+w*x^2)) := by
  by_cases hn : n = 0
  · simp [thetaMixedOneRightJetSeriesTerm, hn]
  · simp only [thetaMixedOneRightJetSeriesTerm, if_neg hn]
    simp only [Nat.cast_one, pow_zero, pow_one, mul_one, one_mul]
    rw [coefficientPolynomial_one_one]
    dsimp [thetaWeightedGaussianIntegrand, thetaGaussianModel,
      thetaWeightedGaussianRightMultiplier]
    simp only [mul_zero, zero_add, add_zero, sub_zero,
      Real.exp_zero, mul_one]
    ring

end W5
