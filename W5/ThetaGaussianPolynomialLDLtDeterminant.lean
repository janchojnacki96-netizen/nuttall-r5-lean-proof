import W5.ThetaAllCoefficientGenericSplitting
import W5.OrderTwoPolynomialCoefficients
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# Symbolic LDLᵀ factorization of the ORIGINAL 5x5 Gaussian B-polynomial matrix

The original coefficientPolynomial i j d q arises from
  exp(-d u) * exp(-q u v) * exp(-d v).
Its finite Taylor coefficient matrix is explicitly a congruence
of a diagonal matrix by a UNIT lower-triangular matrix:

  B(d,q) = L(d) * D(q) * L(d)ᵀ,
  L_ik = if k≤i then (-d)^(i-k)/(i-k)! else 0,
  D_kk = (-q)^k/k!.

We reuse Mathlib's determinant multiplication, transposition,
diagonal and lower-triangular theorems. IF the coefficient
factorization can be verified by finite-ring normalization,
this gives the determinant of ALL FIVE orders immediately;
no nonlinear interval arithmetic is needed for a SINGLE
Gaussian term.

The actual theta certificate is a sum of these matrices MINUS
integral corrections. Signs of individual matrices do NOT
by themselves imply the signs of the sum or its corrections.
-/

namespace W5

/-- Exact unit lower-triangular Taylor shift matrix. -/
noncomputable def thetaPolynomialLower (r : ℕ) (d : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.of (fun i j =>
    if j ≤ i then (-d)^(i.val-j.val) /
      ((i.val-j.val).factorial : ℝ) else 0)

/-- Exact diagonal Taylor coefficient matrix for exp(-q u v). -/
noncomputable def thetaPolynomialDiagonal (r : ℕ) (q : ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  Matrix.diagonal (fun i : Fin r =>
    (-q)^i.val / (i.val.factorial : ℝ))

/-- The Taylor shift is lower triangular, by definition. -/
theorem thetaPolynomialLower_isLowerTriangular (r : ℕ) (d : ℝ) :
    (thetaPolynomialLower r d).IsLowerTriangular := by
  intro i j hij
  have hji : ¬ j ≤ i := not_le.mpr (show i < j from hij)
  simp [thetaPolynomialLower, hji]

/-- All Taylor shift diagonal entries are exactly one. -/
theorem thetaPolynomialLower_diag_one
    (r : ℕ) (d : ℝ) (i : Fin r) :
    thetaPolynomialLower r d i i = 1 := by
  simp [thetaPolynomialLower]

/-- Mathlib's lower-triangular determinant theorem avoids
every factorial and every explicit Leibniz determinant expansion. -/
theorem thetaPolynomialLower_det_one (r : ℕ) (d : ℝ) :
    (thetaPolynomialLower r d).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular
    (thetaPolynomialLower r d)
    (thetaPolynomialLower_isLowerTriangular r d)]
  simp [thetaPolynomialLower_diag_one]

/-- General determinant of the Gaussian LDLᵀ model:
the lower triangular congruence contributes determinant 1. -/
theorem thetaPolynomialLDLt_det
    (r : ℕ) (d q : ℝ) :
    (thetaPolynomialLower r d *
        thetaPolynomialDiagonal r q *
        (thetaPolynomialLower r d).transpose).det =
      ∏ k : Fin r, (-q)^k.val / (k.val.factorial : ℝ) := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  rw [thetaPolynomialLower_det_one]
  simp [thetaPolynomialDiagonal, Matrix.det_diagonal]

/-- Exactly the original coefficientPolynomial, not a
replacement model or formal jet approximation. -/
noncomputable def thetaPolynomialFive (d q : ℝ) :
    Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (fun i j : Fin 5 => coefficientPolynomial i j d q)

set_option maxHeartbeats 2000000

/-- Symbolic finite verification of all 25 coefficient entries.
The remaining simplification is elementary commutative-ring
normalization after expanding Fin 5 sums, using Mathlib tactics. -/
theorem thetaPolynomialFive_LDLt
    (d q : ℝ) :
    thetaPolynomialFive d q =
      thetaPolynomialLower 5 d * thetaPolynomialDiagonal 5 q *
        (thetaPolynomialLower 5 d).transpose := by
  classical
  ext i j
  change coefficientPolynomial i j d q =
    ((thetaPolynomialLower 5 d *
        Matrix.diagonal (fun k : Fin 5 =>
          (-q)^k.val / (k.val.factorial : ℝ))) *
        (thetaPolynomialLower 5 d).transpose) i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [thetaPolynomialLower, coefficientPolynomial,
      Fin.sum_univ_succ, Finset.sum_range_succ] <;> ring

/-- Consequently the genuine full 5x5 single-Gaussian
coefficient determinant is independent of d, and equals
q^10/288 EXACTLY, matching the alternating sign pattern
of the original Nuttall certificate for a single term. -/
theorem thetaPolynomialFive_det_formula
    (d q : ℝ) :
    (thetaPolynomialFive d q).det = q^10 / 288 := by
  rw [thetaPolynomialFive_LDLt, thetaPolynomialLDLt_det]
  norm_num [Fin.prod_univ_succ] <;> ring

/-- Strict positive determinant of the genuine 5x5
single-Gaussian coefficient block when q>0. This is
NOT the Wronskian sign of the full integrated theta kernel. -/
theorem thetaPolynomialFive_det_pos
    (d q : ℝ) (hq : 0 < q) :
    0 < (thetaPolynomialFive d q).det := by
  rw [thetaPolynomialFive_det_formula]
  positivity

end W5
