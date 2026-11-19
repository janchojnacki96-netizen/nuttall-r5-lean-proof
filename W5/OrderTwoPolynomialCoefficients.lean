import W5.OrderTwoThetaCertificateBridge
import W5.ThetaCoefficientSymmetry

/-!
# Explicit leading coefficient polynomials for the theta matrix

The numerical theta coefficient matrix is built from B_ij(d,q).
This module identifies the exact three polynomials at order two:
B_00 = 1, B_01 = -d, B_11 = d^2 - q.

The original analytic matrix and the coefficient matrix are both
symmetric. Accordingly, their order-two identification needs only
three (not four) scalar equalities.

These identities are algebraic and do NOT prove that the theta
coefficient integrals equal derivatives of the original kernel.
-/

namespace W5

theorem coefficientPolynomial_zero_zero (d q : ℝ) :
    coefficientPolynomial (0 : Fin 5) (0 : Fin 5) d q = 1 := by
  norm_num [coefficientPolynomial, Finset.sum_range_succ]

theorem coefficientPolynomial_zero_one (d q : ℝ) :
    coefficientPolynomial (0 : Fin 5) (1 : Fin 5) d q = -d := by
  norm_num [coefficientPolynomial, Finset.sum_range_succ]

theorem coefficientPolynomial_one_zero (d q : ℝ) :
    coefficientPolynomial (1 : Fin 5) (0 : Fin 5) d q = -d := by
  rw [coefficientPolynomial_symmetric]
  exact coefficientPolynomial_zero_one d q

theorem coefficientPolynomial_one_one (d q : ℝ) :
    coefficientPolynomial (1 : Fin 5) (1 : Fin 5) d q = d ^ 2 - q := by
  norm_num [coefficientPolynomial, Finset.sum_range_succ] <;> ring

/-- Only the independent entries (0,0), (0,1), and (1,1)
must be matched with the genuine mixed derivatives. -/
def OrderTwoThreeCoefficientIdentification (x : ℝ) : Prop :=
  analyticCoeff x (0 : Fin 5) (0 : Fin 5) =
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) ∧
  analyticCoeff x (0 : Fin 5) (1 : Fin 5) =
      thetaCoefficient x (0 : Fin 5) (1 : Fin 5) ∧
  analyticCoeff x (1 : Fin 5) (1 : Fin 5) =
      thetaCoefficient x (1 : Fin 5) (1 : Fin 5)

/-- Symmetry reduces the four entrywise identification requirements
to the three independent coefficients. -/
theorem orderTwoIdentification_iff_three (x : ℝ) :
    OrderTwoThetaIdentification x ↔
      OrderTwoThreeCoefficientIdentification x := by
  constructor
  · intro h
    exact ⟨h 0 0, h 0 1, h 1 1⟩
  · rintro ⟨h00, h01, h11⟩ i j
    fin_cases i <;> fin_cases j
    · simpa using h00
    · simpa using h01
    · have h10 :
          analyticCoeff x (1 : Fin 5) (0 : Fin 5) =
            thetaCoefficient x (1 : Fin 5) (0 : Fin 5) := by
        calc
          analyticCoeff x (1 : Fin 5) (0 : Fin 5) =
              analyticCoeff x (0 : Fin 5) (1 : Fin 5) :=
            (analyticCoeff_zero_one_eq_one_zero x).symm
          _ = thetaCoefficient x (0 : Fin 5) (1 : Fin 5) := h01
          _ = thetaCoefficient x (1 : Fin 5) (0 : Fin 5) :=
            thetaCoefficient_symmetric x (0 : Fin 5) (1 : Fin 5)
      simpa using h10
    · simpa using h11

/-- The leading theta determinant is the exact 2 x 2 symmetric
quadratic expression, before any sign inequalities are applied. -/
theorem thetaMatrixTwo_det_three_coefficients (x : ℝ) :
    (thetaMatrixTwo x).det =
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) *
        thetaCoefficient x (1 : Fin 5) (1 : Fin 5) -
      (thetaCoefficient x (0 : Fin 5) (1 : Fin 5)) ^ 2 := by
  rw [Matrix.det_fin_two]
  change
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) *
          thetaCoefficient x (1 : Fin 5) (1 : Fin 5) -
        thetaCoefficient x (0 : Fin 5) (1 : Fin 5) *
          thetaCoefficient x (1 : Fin 5) (0 : Fin 5) =
      thetaCoefficient x (0 : Fin 5) (0 : Fin 5) *
        thetaCoefficient x (1 : Fin 5) (1 : Fin 5) -
      (thetaCoefficient x (0 : Fin 5) (1 : Fin 5)) ^ 2
  rw [← thetaCoefficient_symmetric x (0 : Fin 5) (1 : Fin 5)]
  ring

/-- After three coefficient identifications and a strict theta
minor inequality, the ORIGINAL order-two Wronskian is negative. -/
theorem W_two_negative_of_three_coefficients
    (t : ℝ) (ht : 0 ≤ t)
    (hident : OrderTwoThreeCoefficientIdentification (xOfT t))
    (hdet : (thetaMatrixTwo (xOfT t)).det < 0) :
    W 2 t < 0 :=
  W_two_negative_of_orderTwo_certificate t ht
    ((orderTwoIdentification_iff_three (xOfT t)).mpr hident) hdet

end W5
