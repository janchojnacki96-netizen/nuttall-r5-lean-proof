import W5.ThetaAuditedNormalizedKernelBridge
import W5.NormalizedKernelSymmetry
import W5.ThetaCoefficientSymmetry

/-!
# Reduce 24 independent mixed-jet identifications to 20

The actual normalized Nuttall kernel is symmetric in its two Taylor
variables. The original certificate coefficients are also symmetric.
Consequently the four first-row coefficients (0,j), j=1,...,4,
follow from their already-required first-column counterparts (j,0).

This argument only compares ONE-VARIABLE ordinary iterated derivatives
of equal functions, using the kernel swap identity. It does not
assume Clairaut commutation of arbitrary higher mixed derivatives,
and it does not introduce any unproved analytic jet identification.

The coefficient (0,0) has already been established unconditionally.
Twenty further Gaussian-series Taylor-jet identifications still remain.
-/

namespace W5

/-- Swap the first row and column without any two-variable mixed
derivative interchange: an order-zero derivative is evaluation. -/
theorem analyticCoeff_zero_j_eq_j_zero (x : ℝ) (j : Fin 5) :
    analyticCoeff x (0 : Fin 5) j =
      analyticCoeff x j (0 : Fin 5) := by
  have hswap :
      (fun v : ℝ => normalizedKernel x 0 v) =
      (fun v : ℝ => normalizedKernel x v 0) := by
    funext v
    exact normalizedKernel_swap x 0 v
  unfold analyticCoeff
  simp only [Fin.val_zero, iteratedDeriv_zero,
    Nat.factorial_zero, Nat.cast_one, one_mul, mul_one]
  rw [hswap]

/-- Genuine full 5x5 Taylor/certificate identification reduces to
the 20 entries in rows i=1,2,3,4. The entire first row is already
determined by the proved (0,0) equality and kernel symmetry. -/
theorem thetaTransformCorrect_of_remaining_20_rows
    (hrows : ∀ (x : ℝ), 0 < x → x ≤ (145:ℝ)/256 →
      ∀ (i : Fin 5), i ≠ 0 →
        ∀ (j : Fin 5),
          analyticCoeff x i j = thetaCoefficient x i j) :
    thetaTransformCorrect := by
  intro x hx hbound i j
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      exact analyticCoeff_zero_zero_eq_thetaCoefficient x hx hbound
    · calc
        analyticCoeff x (0 : Fin 5) j =
            analyticCoeff x j 0 :=
          analyticCoeff_zero_j_eq_j_zero x j
        _ = thetaCoefficient x j 0 :=
          hrows x hx hbound j hj 0
        _ = thetaCoefficient x 0 j :=
          (thetaCoefficient_symmetric x j 0).symm
  · exact hrows x hx hbound i hi j

/-- The remaining twenty obligations can be stated entirely in
terms of the ACTUAL full Gaussian series and its mixed jets:
the local kernel-to-series bridge is already proved for all orders. -/
theorem thetaTransformCorrect_of_remaining_20_gaussian_jets
    (hrows : ∀ (x : ℝ), 0 < x → x ≤ (145:ℝ)/256 →
      ∀ (i : Fin 5), i ≠ 0 →
        ∀ (j : Fin 5),
          thetaCertificateGaussianAnalyticCoeff x i j =
            thetaCoefficient x i j) :
    thetaTransformCorrect := by
  apply thetaTransformCorrect_of_remaining_20_rows
  intro x hx hbound i hi j
  rw [analyticCoeff_eq_thetaCertificateGaussianAnalyticCoeff
    x hx hbound i j]
  exact hrows x hx hbound i hi j

end W5
