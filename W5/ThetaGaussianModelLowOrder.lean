import W5.OrderTwoPolynomialCoefficients

/-!
# The analytic mixed jet of the elementary theta Gaussian model

The transformed theta integral is built from
  exp (-d*(u+v) - q*u*v).
Its Taylor coefficients of degrees (0,0), (0,1), and (1,1)
must equal the explicit polynomials B00, B01, B11.

The following proofs are ordinary real-variable differentiations.
They establish the low-order model identity without an external
numerical certificate. Moving these derivatives through the original
infinite sum and the w-integral remains a separate analytic task.
-/

namespace W5

noncomputable def thetaGaussianModel (d q u v : ℝ) : ℝ :=
  Real.exp (-d * (u + v) - q * u * v)

theorem thetaGaussianModel_zero_zero (d q : ℝ) :
    thetaGaussianModel d q 0 0 = 1 := by
  simp [thetaGaussianModel]

theorem thetaGaussianModel_right_hasDerivAt
    (d q u v : ℝ) :
    HasDerivAt (fun w : ℝ => thetaGaussianModel d q u w)
      ((-d - q*u) * thetaGaussianModel d q u v) v := by
  have harg : HasDerivAt
      (fun w : ℝ => -d*(u+w) - q*u*w) (-d-q*u) v := by
    have h := ((hasDerivAt_id v).const_mul (-d-q*u)).const_add (-d*u)
    convert h using 1 <;> (first | (funext w; ring) | ring)
  have h := (Real.hasDerivAt_exp (-d*(u+v) - q*u*v)).comp v harg
  convert h using 1 <;>
    simp only [thetaGaussianModel, Function.comp_def] <;> ring

theorem thetaGaussianModel_right_deriv_zero (d q u : ℝ) :
    deriv (fun v : ℝ => thetaGaussianModel d q u v) 0 =
      (-d-q*u) * Real.exp (-d*u) := by
  have h := (thetaGaussianModel_right_hasDerivAt d q u 0).deriv
  simpa [thetaGaussianModel] using h

theorem thetaGaussianModel_mixed_deriv_zero (d q : ℝ) :
    deriv (fun u : ℝ =>
      deriv (fun v : ℝ => thetaGaussianModel d q u v) 0) 0 =
        d^2 - q := by
  have hfun :
      (fun u : ℝ =>
        deriv (fun v : ℝ => thetaGaussianModel d q u v) 0) =
      (fun u : ℝ => (-d-q*u) * Real.exp (-d*u)) := by
    funext u
    exact thetaGaussianModel_right_deriv_zero d q u
  rw [hfun]
  have hlin : HasDerivAt (fun u : ℝ => -d-q*u) (-q) 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).const_mul (-q)).const_add (-d)
    convert h using 1 <;> (first | (funext u; ring) | ring)
  have hscale : HasDerivAt (fun u : ℝ => -d*u) (-d) 0 := by
    simpa only [id_eq] using
      ((hasDerivAt_id (0:ℝ)).const_mul (-d))
  have hexp : HasDerivAt (fun u : ℝ => Real.exp (-d*u)) (-d) 0 := by
    have h := (Real.hasDerivAt_exp (-d*(0:ℝ))).comp (0:ℝ) hscale
    simpa only [Function.comp_def, mul_zero, Real.exp_zero, one_mul] using h
  have hp := (hlin.mul hexp).deriv
  convert hp using 1 <;> simp <;> ring

theorem thetaGaussianModel_zero_zero_eq_polynomial (d q : ℝ) :
    thetaGaussianModel d q 0 0 =
      coefficientPolynomial (0 : Fin 5) (0 : Fin 5) d q := by
  rw [thetaGaussianModel_zero_zero, coefficientPolynomial_zero_zero]

theorem thetaGaussianModel_zero_one_eq_polynomial (d q : ℝ) :
    deriv (fun v : ℝ => thetaGaussianModel d q 0 v) 0 =
      coefficientPolynomial (0 : Fin 5) (1 : Fin 5) d q := by
  rw [thetaGaussianModel_right_deriv_zero, coefficientPolynomial_zero_one]
  simp

theorem thetaGaussianModel_one_one_eq_polynomial (d q : ℝ) :
    deriv (fun u : ℝ =>
      deriv (fun v : ℝ => thetaGaussianModel d q u v) 0) 0 =
        coefficientPolynomial (1 : Fin 5) (1 : Fin 5) d q := by
  rw [thetaGaussianModel_mixed_deriv_zero, coefficientPolynomial_one_one]

end W5
