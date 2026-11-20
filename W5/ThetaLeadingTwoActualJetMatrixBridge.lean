import W5.ThetaB10B01FullCoefficientSplitting

/-!
# The numerical leading 2x2 theta matrix from genuine Gaussian jets

The earlier lemmas proved four exact scalar identities for the
original numerical coefficients thetaCoefficient[0..1,0..1].
They rigorously separated the elementary square-index Gaussian
base part and identified the integral corrections with the
ACTUAL zeroth, first and mixed derivatives of the full infinite
transformed Gaussian theta series.

This module packages the four independent scalar statements into
a single entrywise equality for the numerical 2x2 theta matrix.
It is NOT an equality with the original Nuttall normalizedKernel:
that analytic identification still requires a separate proof.
It also does not establish the sign of the 2x2 determinant.
-/

namespace W5

/-- The genuine zeroth, first or mixed derivative at the Taylor
origin of the entire integrated Gaussian theta series, selected
by one of the four entries of the leading matrix. In particular
(0,1) is the actual RIGHT derivative, not a formal symmetric
placeholder. -/
noncomputable def thetaActualGaussianJetTwo (x : ℝ)
    (i j : Fin 2) : ℝ :=
  if i = 0 then
    if j = 0 then
      ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n 0
    else
      deriv (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x 0 n z) 0
  else
    if j = 0 then
      deriv (fun z : ℝ =>
        ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n 0) 0
    else
      deriv (fun z : ℝ =>
        iteratedDeriv 1
          (fun y : ℝ =>
            ∑' n : ℕ, thetaGaussianIntegratedSeriesTerm x z n y) 0) 0

/-- The elementary, separately summable, original square-index
Gaussian contribution to the leading numerical theta matrix. -/
noncomputable def thetaCertificateBaseMatrixTwo (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j =>
    ∑' n : ℕ,
      thetaCertificateBaseTerm x
        (⟨i.val, by omega⟩ : Fin 5)
        (⟨j.val, by omega⟩ : Fin 5) n)

/-- The actual 2x2 matrix of genuine zeroth, first, and
mixed Gaussian derivatives of the full transformed series. -/
noncomputable def thetaActualGaussianJetMatrixTwo (x : ℝ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j => thetaActualGaussianJetTwo x i j)

/-- Each of the four leading original theta certificate entries
is the elementary square-index base term minus x²/4 times a
GENUINE transformed Gaussian series derivative. The (0,1)
identity uses the already verified equality of first right
and first left derivatives at the symmetric Taylor origin. -/
theorem thetaMatrixTwo_entry_eq_base_sub_actualGaussianJet
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (i j : Fin 2) :
    thetaCoefficient x (⟨i.val, by omega⟩ : Fin 5)
        (⟨j.val, by omega⟩ : Fin 5) =
      (∑' n : ℕ,
        thetaCertificateBaseTerm x
          (⟨i.val, by omega⟩ : Fin 5)
          (⟨j.val, by omega⟩ : Fin 5) n) -
      (x^2/4) * thetaActualGaussianJetTwo x i j := by
  fin_cases i <;> fin_cases j
  · simpa [thetaActualGaussianJetTwo] using
      (thetaCoefficient_zero_zero_eq_base_minus_integrated x hx hx1)
  · have h :=
      thetaCoefficient_zero_one_eq_base_minus_actual_left_derivative
        x hx hx1
    rw [← thetaGaussianIntegratedSeries_deriv_right_eq_left_at_origin x] at h
    simpa [thetaActualGaussianJetTwo] using h
  · simpa [thetaActualGaussianJetTwo] using
      (thetaCoefficient_one_zero_eq_base_minus_actual_left_derivative
        x hx hx1)
  · simpa [thetaActualGaussianJetTwo] using
      (thetaCoefficient_one_one_eq_base_minus_actual_mixed_derivative
        x hx hx1)

/-- Exact matrix-level analytic representation of the original
NUMERICAL leading 2x2 theta certificate: elementary Gaussian
base matrix minus x²/4 times the genuine transformed theta
Gaussian jet matrix.

This is the full leading 2x2 CERTIFICATE representation, not
the still-unproved analyticCoeff = thetaCoefficient bridge. -/
theorem thetaMatrixTwo_eq_baseMatrix_sub_actualGaussianJetMatrix
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaMatrixTwo x =
      Matrix.of (fun i j =>
        thetaCertificateBaseMatrixTwo x i j -
          (x^2/4) * thetaActualGaussianJetMatrixTwo x i j) := by
  ext i j
  simpa [thetaMatrixTwo, thetaCertificateBaseMatrixTwo,
    thetaActualGaussianJetMatrixTwo] using
    thetaMatrixTwo_entry_eq_base_sub_actualGaussianJet x hx hx1 i j

end W5
