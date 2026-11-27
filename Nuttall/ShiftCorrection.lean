import Nuttall.ShiftGeometricPrefix

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- Polynomial replacement for the multiplier
((1-w)^{-1}+(1-z)^{-1}-1-d) through degree (k-1) in each variable. -/
noncomputable def shiftCorrectionMultiplier (k : ℕ) (d : ℝ) : (ℝ[X])[X] :=
  shiftGeometricPrefix k + C (shiftGeometricPrefix k) - C (C (1+d))

/-- Clearing the denominators leaves errors with a factor (w^k) or (z^k). -/
theorem shiftCorrectionMultiplier_clear (k : ℕ) (d : ℝ) :
    (1-X) * (1-C X) * shiftCorrectionMultiplier k d =
      bilinearPolynomial (1-d) d d (-(1+d)) -
        X^k * (1-C X) - C (X^k) * (1-X) := by
  have hz : C (shiftGeometricPrefix k : ℝ[X]) * (1-C X) =
      1 - (C (X^k) : (ℝ[X])[X]) := by
    have h := congrArg (C : ℝ[X] →+* (ℝ[X])[X])
      (shiftGeometricPrefix_mul_one_sub (R := ℝ) k)
    simpa only [map_sub, map_mul, map_one] using h
  calc
    _ = (shiftGeometricPrefix k * (1-X)) * (1-C X) +
        (C (shiftGeometricPrefix k) * (1-C X)) * (1-X) -
        C (C (1+d)) * (1-X) * (1-C X) := by
      unfold shiftCorrectionMultiplier
      ring
    _ = _ := by
      rw [shiftGeometricPrefix_mul_one_sub, hz, bilinearPolynomial_shift, map_add, map_add,
        map_one, map_one]
      ring

/-- The triangular factor with its diagonal correction in Section 4.2. -/
noncomputable def shiftCorrectionMatrix (M k : ℕ) (d : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  shiftTriangular M k - ((1+d)/2) • (1 : Matrix (Fin k) (Fin k) ℝ)

private theorem normalize_correction_split {M k : ℕ} (P : (ℝ[X])[X]) (d : ℝ) :
    normalizedShiftCoefficients M k (shiftCorrectionMultiplier k d * P) =
      normalizedShiftCoefficients M k (shiftGeometricPrefix k * P) +
      normalizedShiftCoefficients M k (C (shiftGeometricPrefix k) * P) -
      (1+d) • normalizedShiftCoefficients M k P := by
  ext i j
  simp only [shiftCorrectionMultiplier, normalizedShiftCoefficients, add_mul, sub_mul,
    Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.of_apply, coeff_add, coeff_sub, coeff_C_mul, add_div, sub_div]
  ring

/-- In the normalized basis the correction multiplier acts as (Pmapsto V_dP+PV_d^\top). -/
theorem normalizedShiftCoefficients_correction {M k : ℕ} (hk : k ≤ M+1)
    (P : (ℝ[X])[X]) (d : ℝ) :
    normalizedShiftCoefficients M k (shiftCorrectionMultiplier k d * P) =
      shiftCorrectionMatrix M k d * normalizedShiftCoefficients M k P +
        normalizedShiftCoefficients M k P * (shiftCorrectionMatrix M k d).transpose := by
  rw [normalize_correction_split, normalizedShiftCoefficients_geometric_left hk,
    normalizedShiftCoefficients_geometric_right hk]
  unfold shiftCorrectionMatrix
  simp only [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, sub_mul,
    mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The coefficient expression gives the corrected matrix (A_d) before
identifying it with the normalized Hankel transform. -/
theorem normalized_shifted_polynomial_with_correction {M k : ℕ} (hk : k ≤ M+1) (u d : ℝ) :
    let P := (bilinearPolynomial (1-d) d d (-(1+d)))^M
    normalizedShiftCoefficients M k (P - C (C (u/(M+1))) * (shiftCorrectionMultiplier k d * P)) =
      shiftCore M k d - (u/(M+1)) •
        (shiftCorrectionMatrix M k d * shiftCore M k d +
          shiftCore M k d * (shiftCorrectionMatrix M k d).transpose) := by
  let P := (bilinearPolynomial (1-d) d d (-(1+d)))^M
  change normalizedShiftCoefficients M k (_ : (ℝ[X])[X]) = _
  have hcore : normalizedShiftCoefficients M k P = shiftCore M k d := rfl
  rw [← hcore, ← normalizedShiftCoefficients_correction hk]
  ext i j
  simp only [normalizedShiftCoefficients, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
    smul_eq_mul, coeff_sub, coeff_C_mul, sub_div, mul_div_assoc]
  rfl

#print axioms shiftCorrectionMultiplier_clear
#print axioms normalizedShiftCoefficients_correction
#print axioms normalized_shifted_polynomial_with_correction

end Nuttall
