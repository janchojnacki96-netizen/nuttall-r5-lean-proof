import Nuttall.ShiftHankelPower
import Nuttall.ShiftHankelTruncation
import Nuttall.ShiftedMomentDerivatives

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- The matrix (A_d) of one summand with the correction included. -/
noncomputable def correctedShiftCore (M k : ℕ) (u d : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  shiftCore M k d - (u/(M+1)) •
    (shiftCorrectionMatrix M k d * shiftCore M k d +
      shiftCore M k d * (shiftCorrectionMatrix M k d).transpose)

private theorem normalizedShiftCoefficients_const_mul (M k : ℕ) (q : ℝ) (P : (ℝ[X])[X]) :
    normalizedShiftCoefficients M k (C (C q) * P) = q • normalizedShiftCoefficients M k P := by
  ext i j
  simp only [normalizedShiftCoefficients, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul,
    coeff_C_mul, mul_div_assoc]

private theorem hankelPowerPolynomial_block {M k : ℕ} (hk : 2*(k-1) ≤ M) (u d : ℝ) :
    ShiftCoeffEq k
      (shiftHankelPolynomial M k u (hankelPowerMatrix M k (u*(1-d))))
      (C (C (u^M / (M.factorial : ℝ))) * (bilinearPolynomial (1-d) d d (-(1+d)))^M) := by
  intro i j
  simp only [coeff_C_mul]
  exact hankelPowerMatrix_coeff hk u d i j

/-- For an individual summand, the triangular transform of the Hankel
matrix of tail weights is the corrected coefficient matrix times (u^M/M!). -/
theorem shiftHankel_single_congruence {M k : ℕ} (hk : 2*(k-1) ≤ M) (u d : ℝ) :
    let H := Matrix.of fun a b : Fin k => tailMomentWeight (M-(a.val+b.val)) (u*(1-d))
    let S := shiftHankelBasis M k u
    S * H * S.transpose = (u^M / (M.factorial : ℝ)) • correctedShiftCore M k u d := by
  let s := u*(1-d)
  let B := bilinearPolynomial (1-d) d d (-(1+d))
  let q := u^M / (M.factorial : ℝ)
  let G : (ℝ[X])[X] := shiftGeometricPrefix k * C (shiftGeometricPrefix k)
  have hk' : k ≤ M+1 := by omega
  have hentry : (Matrix.of fun (a b : Fin k) => tailMomentWeight (M-(a.val+b.val)) s) =
      hankelPowerMatrix M k s - hankelPowerMatrix (M+1) k s := by
    ext a b
    have ha := a.isLt
    have hb := b.isLt
    simp only [Matrix.of_apply, Matrix.sub_apply, hankelPowerMatrix, tailMomentWeight]
    rw [show M-(a.val+b.val)+1 = (M+1)-(a.val+b.val) by omega]
  change shiftHankelBasis M k u * (Matrix.of fun a b : Fin k =>
    tailMomentWeight (M-(a.val+b.val)) s) * (shiftHankelBasis M k u).transpose = _
  rw [← normalizedShiftCoefficients_hankelPolynomial, hentry, shiftHankelPolynomial_sub]
  have hbase := hankelPowerPolynomial_block hk u d
  have hnext := hankelPowerPolynomial_block (M := M+1) (k := k) (by omega) u d
  have hprefix := (shiftHankelPolynomial_succ_prefix hk' u (hankelPowerMatrix (M+1) k s)).symm
  have hcorr := (geometricPrefix_shiftForm (k := k) d (B^M)).mul (C (C (u^(M+1) / ((M+1).factorial : ℝ))))
  have hf : u^(M+1) / ((M+1).factorial : ℝ) = q * (u/(M+1)) := by
    dsimp [q]
    rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    field_simp
  have hp :
      ShiftCoeffEq k (shiftHankelPolynomial M k u (hankelPowerMatrix (M+1) k s))
        (C (C (q*(u/(M+1)))) * (shiftCorrectionMultiplier k d * B^M)) := by
    have h := hprefix.trans (hnext.mul G)
    have he : G * (C (C (u^(M+1) / ((M+1).factorial : ℝ))) * B^(M+1)) =
        C (C (u^(M+1) / ((M+1).factorial : ℝ))) * (G * (B * B^M)) := by
      rw [pow_succ B M]
      ac_rfl
    rw [he] at h
    exact (h.trans hcorr).trans (by rw [hf]; exact fun _ _ => rfl)
  have h := (hbase.sub hp).normalized M
  rw [h]
  change normalizedShiftCoefficients M k (C (C q) * B^M -
    C (C (q*(u/(M+1)))) * (shiftCorrectionMultiplier k d * B^M)) = _
  rw [show C (C q) * B^M - C (C (q*(u/(M+1)))) * (shiftCorrectionMultiplier k d * B^M) =
      C (C q) * (B^M - C (C (u/(M+1))) * (shiftCorrectionMultiplier k d * B^M)) by
    simp only [map_mul]; ring, normalizedShiftCoefficients_const_mul,
    normalized_shifted_polynomial_with_correction hk']
  rfl

/-- The Hankel matrix of the shifted moments appearing after reversing the Wronskian columns. -/
noncomputable def shiftedMomentHankel (M k : ℕ) (u : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a b => shiftedMoment (M-(a.val+b.val)) u

/-- The corrected matrices summed over precisely the active theta indices. -/
noncomputable def summedCorrectedShiftCore (M k : ℕ) (u : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  ∑ n ∈ activeThetaIndices u,
    (Real.sqrt (n : ℝ))⁻¹ • correctedShiftCore M k u (thetaKnot n / u)

/-- The entire shifted Hankel block transforms to the sum of corrected matrices. -/
theorem shiftHankel_congruence {M k : ℕ} (hk : 2*(k-1) ≤ M) {u : ℝ} (hu : 0 < u) :
    let S := shiftHankelBasis M k u
    S * shiftedMomentHankel M k u * S.transpose =
      (u^M / (M.factorial : ℝ)) • summedCorrectedShiftCore M k u := by
  let H (n : ℕ) : Matrix (Fin k) (Fin k) ℝ := Matrix.of fun a b =>
    tailMomentWeight (M-(a.val+b.val)) (u-thetaKnot n)
  have hmat : shiftedMomentHankel M k u =
      ∑ n ∈ activeThetaIndices u, (Real.sqrt (n : ℝ))⁻¹ • H n := by
    ext i j
    simp only [shiftedMomentHankel, Matrix.of_apply, shiftedMoment_eq_sum_active, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul, H, div_eq_mul_inv]
    apply Finset.sum_congr rfl
    intro n _
    exact mul_comm _ _
  change shiftHankelBasis M k u * shiftedMomentHankel M k u * (shiftHankelBasis M k u).transpose = _
  rw [hmat, summedCorrectedShiftCore]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have heq : u*(1-thetaKnot n/u) = u-thetaKnot n := by field_simp
  have h := shiftHankel_single_congruence hk u (thetaKnot n/u)
  simp only [heq] at h
  rw [show shiftHankelBasis M k u * H n * (shiftHankelBasis M k u).transpose = _ from h]
  simp only [smul_smul, mul_comm ((Real.sqrt (n : ℝ))⁻¹)]

/-- The positive basis determinant and positive scalar preserve the sign. -/
theorem shiftedMomentHankel_weighted_det_pos_iff {M k : ℕ} (hk : 2*(k-1) ≤ M)
    {u : ℝ} (hu : 0 < u) (c : ℝ) :
    0 < c * (shiftedMomentHankel M k u).det ↔ 0 < c * (summedCorrectedShiftCore M k u).det := by
  let S := shiftHankelBasis M k u
  have hs : 0 < S.det := det_shiftHankelBasis_pos (by omega) hu
  have hq : 0 < (u^M / (M.factorial : ℝ))^k := by positivity
  have h := congrArg Matrix.det (shiftHankel_congruence hk hu)
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Fintype.card_fin] at h
  change S.det * (shiftedMomentHankel M k u).det * S.det =
    (u^M / (M.factorial : ℝ))^k * (summedCorrectedShiftCore M k u).det at h
  have hc : S.det * (c * (shiftedMomentHankel M k u).det) * S.det =
      (u^M / (M.factorial : ℝ))^k * (c * (summedCorrectedShiftCore M k u).det) := by
    rw [show S.det * (c * (shiftedMomentHankel M k u).det) * S.det =
      c * (S.det * (shiftedMomentHankel M k u).det * S.det) by ring, h]
    ring
  rw [← mul_pos_iff_of_pos_left hs, ← mul_pos_iff_of_pos_right hs, hc,
    mul_pos_iff_of_pos_left hq]

#print axioms shiftHankel_single_congruence
#print axioms shiftHankel_congruence
#print axioms shiftedMomentHankel_weighted_det_pos_iff

end Nuttall
