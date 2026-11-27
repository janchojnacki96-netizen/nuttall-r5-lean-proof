import Nuttall.ShiftCore
import Mathlib.LinearAlgebra.Matrix.Notation

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- Substituting (sw,sz) multiplies the coefficient at ((i,j)) by (s^{i+j}). -/
theorem bilinearCoeff_scale (M i j : ℕ) (a b c e s : ℝ) :
    bilinearCoeff M a (s*b) (s*c) (s*s*e) i j =
      s^(i+j) * bilinearCoeff M a b c e i j := by
  simp only [bilinearCoeff, coeff_bilinearPolynomial_pow]
  have ha : C a + C (s*b) * X = (C a + C b * X).comp (C s * X) := by
    simp only [map_mul, add_comp, mul_comp, C_comp, X_comp]
    ring
  have hc : C (s*c) + C (s*s*e) * X =
      C s * (C c + C e * X).comp (C s * X) := by
    simp only [map_mul, add_comp, mul_comp, C_comp, X_comp]
    ring
  let Q := (C c + C e * X)^i * (C a + C b * X)^(M-i) * C (M.choose i : ℝ)
  have hQ : (C (s*c) + C (s*s*e) * X)^i *
      (C a + C (s*b) * X)^(M-i) * C (M.choose i : ℝ) =
      C (s^i) * Q.comp (C s * X) := by
    simp only [ha, hc, mul_pow, ← C_pow, Q, mul_comp, pow_comp, C_comp]
    ring
  rw [hQ, coeff_C_mul, comp_C_mul_X_coeff, pow_add]
  change s^i * (Q.coeff j * s^j) = s^i * s^j * Q.coeff j
  ring

/-- Multiplying the whole bilinear form by (s) multiplies its powered coefficients by (s^M). -/
theorem bilinearCoeff_const_mul (M i j : ℕ) (a b c e s : ℝ) :
    bilinearCoeff M (s*a) (s*b) (s*c) (s*e) i j = s^M * bilinearCoeff M a b c e i j := by
  have h : bilinearPolynomial (s*a) (s*b) (s*c) (s*e) =
      C (C s) * bilinearPolynomial a b c e := by
    unfold bilinearPolynomial
    simp only [← C_mul_X_eq_monomial, map_mul, map_add]
    ring
  simp only [bilinearCoeff, h, mul_pow, ← C_pow, coeff_C_mul]

noncomputable def shiftScale (d : ℝ) : ℝ := Real.sqrt ((1-d)/(1+d))

noncomputable def shiftCosine (d : ℝ) : ℝ := Real.sqrt (1-d^2)

theorem shiftScale_pos {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d < 1) :
    0 < shiftScale d := by
  apply Real.sqrt_pos.2
  exact div_pos (sub_pos.2 hd₁) (by linarith)

theorem shiftCosine_sq_add_sq {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    (shiftCosine d)^2 + d^2 = 1 := by
  have h : 0 ≤ 1-d^2 := by nlinarith [mul_nonneg (sub_nonneg.2 hd₁) (show 0 ≤ 1+d by linarith)]
  rw [shiftCosine, Real.sq_sqrt h]
  ring

theorem shiftScale_mul_shiftCosine {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    shiftScale d * shiftCosine d = 1-d := by
  have h₁ : 0 ≤ 1-d := sub_nonneg.2 hd₁
  have h₂ : 0 < 1+d := by linarith
  have h₃ : 1-d^2 = (1+d)*(1-d) := by ring
  rw [shiftScale, shiftCosine, ← Real.sqrt_mul (div_nonneg h₁ h₂.le), h₃]
  have h : (1-d)/(1+d)*((1+d)*(1-d)) = (1-d)^2 := by
    field_simp
  rw [h, Real.sqrt_sq h₁]

/-- The degree-one form used in the symmetric power is orthogonal. -/
theorem shiftReflection_mul_transpose {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![shiftCosine d, d; d, -shiftCosine d]
    B * B.transpose = 1 := by
  dsimp
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    nlinarith only [shiftCosine_sq_add_sq hd₀ hd₁]

/-- The normalized coefficients of the (M)-th symmetric power of the reflection. -/
noncomputable def shiftReflectionPower (M k : ℕ) (d : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => bilinearCoeff M (shiftCosine d) d d (-shiftCosine d) i.val j.val /
    Real.sqrt ((M.choose i.val : ℝ) * (M.choose j.val : ℝ))

/-- The diagonal scaling factors on the two sides of the powered bilinear form. -/
theorem shiftCore_eq_scaled_reflectionPower {M k : ℕ} {d : ℝ}
    (hd₀ : 0 ≤ d) (hd₁ : d < 1) (hM : 2*(k-1) ≤ M) (i j : Fin k) :
    shiftCore M k d i j =
      shiftScale d ^ (M-(i.val+j.val)) * shiftReflectionPower M k d i j := by
  let s := shiftScale d
  have hs : 0 < s := shiftScale_pos hd₀ hd₁
  have hsc : s * shiftCosine d = 1-d := shiftScale_mul_shiftCosine hd₀ hd₁.le
  have hs2 : s^2 * (1+d) = 1-d := by
    dsimp [s, shiftScale]
    rw [Real.sq_sqrt (div_nonneg (by linarith) (by linarith))]
    field_simp
  have hse : s*s*(-(1+d)) = s * (-shiftCosine d) := by nlinarith [hs2, hsc]
  have hscaled : bilinearCoeff M (1-d) (s*d) (s*d) (s*s*(-(1+d))) i.val j.val =
      s^M * bilinearCoeff M (shiftCosine d) d d (-shiftCosine d) i.val j.val := by
    rw [hse, ← hsc, bilinearCoeff_const_mul]
  have h := (bilinearCoeff_scale M i.val j.val (1-d) d d (-(1+d)) s).symm.trans hscaled
  have hij : i.val+j.val ≤ M := by have := i.isLt; have := j.isLt; omega
  have hraw :
      bilinearCoeff M (1-d) d d (-(1+d)) i.val j.val =
        s^(M-(i.val+j.val)) * bilinearCoeff M (shiftCosine d) d d (-shiftCosine d) i.val j.val := by
    apply (mul_left_cancel₀ (show s^(i.val+j.val) ≠ 0 from pow_ne_zero _ hs.ne'))
    rw [h, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hij]
  simp only [shiftCore, shiftReflectionPower, Matrix.of_apply, hraw, mul_div_assoc, s]

/-- The exponent left after extracting both diagonal weights identifies the critical block. -/
theorem shift_residual_exponent {r p k : ℕ} (hk : 1 ≤ k) (hkp : k ≤ p) (hpr : p ≤ r) :
    2*r-p+k-2-2*(k-1) = 2*r-p-k ∧ (2*r-p-k = 0 ↔ p = r ∧ k = r) := by
  omega

#print axioms bilinearCoeff_scale
#print axioms shiftReflection_mul_transpose
#print axioms shiftCore_eq_scaled_reflectionPower
#print axioms shift_residual_exponent

end Nuttall
