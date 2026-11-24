import W5.NormalizedKernelSymmetry
import W5.ThetaAuditedNormalizedKernelBridge

/-!
# Four fewer independent analytic theta-jet obligations

The normalized Nuttall kernel is exactly symmetric in its two
variables. Whenever one Taylor index is zero, the (0,k) and (k,0)
derivatives therefore coincide for EVERY k, without commuting mixed
derivatives or assuming higher smoothness. The original real theta
coefficient matrix is already proved symmetric as well.

The original (0,0) coefficient equality is already unconditional.
Consequently all 25 kernel/certificate coefficient identities
reduce to the 20 with the SECOND index nonzero. This replaces the
earlier 24-jet conditional target without introducing any axiom.
The remaining 20 identities are genuine, unproved obligations.
-/

namespace W5

/-- Uniformly for k=0,...,4, swapping the nonzero Taylor coordinate
does not change the analytic coefficient. The identity only compares
pure univariate derivatives, never mixed derivative orders. -/
theorem analyticCoeff_zero_k_eq_k_zero
    (x : ℝ) (k : Fin 5) :
    analyticCoeff x (0 : Fin 5) k =
      analyticCoeff x k (0 : Fin 5) := by
  have hswap :
      (fun z : ℝ => normalizedKernel x 0 z) =
      (fun z : ℝ => normalizedKernel x z 0) := by
    funext z
    exact normalizedKernel_swap x 0 z
  simp only [analyticCoeff, iteratedDeriv_zero,
    Fin.val_zero, Nat.factorial_zero, Nat.cast_one,
    one_mul, mul_one]
  rw [hswap]

/-- An unconditional 25-to-20 reduction: prove just the 20
coefficients with j>0, and obtain all four (i,0), i>0, by
the exact kernel and original theta matrix symmetries.
The already proved (0,0) case completes the last entry. -/
theorem thetaTransformCorrect_of_last20_gaussian_jets
    (h20 :
      ∀ x : ℝ, 0 < x → x ≤ (145 : ℝ) / 256 →
        ∀ i j : Fin 5, j ≠ 0 →
          thetaCertificateGaussianAnalyticCoeff x i j =
            thetaCoefficient x i j) :
    thetaTransformCorrect := by
  intro x hx hb i j
  rw [analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
    x hx hb i j]
  by_cases hj : j = 0
  · subst j
    by_cases hi : i = 0
    · subst i
      exact thetaCertificateGaussianAnalyticCoeff_zero_zero_eq_theta
        x hx hb
    · calc
        thetaCertificateGaussianAnalyticCoeff x i 0 =
            analyticCoeff x i 0 :=
          (analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
            x hx hb i 0).symm
        _ = analyticCoeff x 0 i :=
          (analyticCoeff_zero_k_eq_k_zero x i).symm
        _ = thetaCertificateGaussianAnalyticCoeff x 0 i :=
          analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
            x hx hb 0 i
        _ = thetaCoefficient x 0 i := h20 x hx hb 0 i hi
        _ = thetaCoefficient x i 0 :=
          thetaCoefficient_symmetric x 0 i
  · exact h20 x hx hb i j hj

end W5
