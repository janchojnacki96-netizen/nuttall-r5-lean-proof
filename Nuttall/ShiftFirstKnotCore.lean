import Nuttall.ShiftCore
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

namespace Nuttall

open Polynomial
open scoped Polynomial

private theorem coeff_linear_power (a : ℝ) (i j : ℕ) :
    ((1 + C a * X)^i : ℝ[X]).coeff j = (i.choose j : ℝ) * a^j := by
  have hcomp : ((1 + X)^i : ℝ[X]).comp (C a * X) = (1 + C a * X)^i := by simp
  rw [← hcomp, comp_C_mul_X_coeff, coeff_one_add_X_pow]

/-- At the first positive knot, the new summand has shift one.
Its coefficient uses the degree left after the forced factor of (z^(M-i)). -/
theorem bilinearCoeff_shift_one (M i j : ℕ) :
    bilinearCoeff M 0 1 1 (-2) i j =
      if M-i ≤ j then (i.choose (j-(M-i)) : ℝ) * (-2)^(j-(M-i)) * (M.choose i : ℝ)
      else 0 := by
  rw [bilinearCoeff, coeff_bilinearPolynomial_pow, coeff_mul_C]
  simp only [map_zero, map_one, zero_add, one_mul, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_linear_power]
  · exact zero_mul _

/-- Below total degree (M), the normalized shift-one coefficient is zero. -/
theorem shiftCore_one_eq_zero_of_add_lt {M k : ℕ} (i j : Fin k)
    (h : i.val+j.val < M) : shiftCore M k 1 i j = 0 := by
  simp only [shiftCore, Matrix.of_apply, sub_self]
  rw [show -(1+(1:ℝ)) = -2 by norm_num, bilinearCoeff_shift_one,
    ite_eq_right (by omega), zero_div]

/-- At total degree (M), the two binomial normalizations agree and cancel. -/
theorem shiftCore_one_eq_one_of_add_eq {M k : ℕ} (i j : Fin k)
    (h : i.val+j.val = M) : shiftCore M k 1 i j = 1 := by
  have hi : i.val ≤ M := by omega
  have hij : M-i.val = j.val := by omega
  have hchoose : M.choose j.val = M.choose i.val := by
    simpa only [hij] using Nat.choose_symm hi
  have hp : 0 < (M.choose i.val : ℝ) := by exact_mod_cast Nat.choose_pos hi
  simp only [shiftCore, Matrix.of_apply, sub_self]
  rw [show -(1+(1:ℝ)) = -2 by norm_num, bilinearCoeff_shift_one, hij, ite_eq_left le_rfl,
    Nat.sub_self, Nat.choose_zero_right, pow_zero, Nat.cast_one, mul_one, one_mul, hchoose,
    ← sq, Real.sqrt_sq hp.le, div_self hp.ne']

/-- The last diagonal coefficient of the shift-one block in Theorem 6.3. -/
theorem shiftCore_one_last_diagonal {l : ℕ} (hl : 1 ≤ l) :
    shiftCore (2*l-1) (l+1) 1 (Fin.last l) (Fin.last l) = -2*(l:ℝ) := by
  have hi : l ≤ 2*l-1 := by omega
  have hsub : l-(2*l-1-l) = 1 := by omega
  have hp : 0 < ((2*l-1).choose l : ℝ) := by exact_mod_cast Nat.choose_pos hi
  simp only [shiftCore, Matrix.of_apply, Fin.val_last, sub_self]
  rw [show -(1+(1:ℝ)) = -2 by norm_num, bilinearCoeff_shift_one, ite_eq_left (by omega),
    hsub, Nat.choose_one_right, pow_one, ← sq, Real.sqrt_sq hp.le]
  rw [mul_div_cancel_right₀ _ hp.ne']
  ring

/-- The shift-one block has only its bottom-right diagonal entry and the
two adjacent off-diagonal entries. -/
theorem shiftCore_one_firstKnot_entries {l : ℕ} (hl : 1 ≤ l) (i j : Fin (l+1)) :
    shiftCore (2*l-1) (l+1) 1 i j =
      if i.val = l ∧ j.val = l then -2*(l:ℝ)
      else if i.val+j.val = 2*l-1 then 1 else 0 := by
  by_cases hlast : i.val = l ∧ j.val = l
  · rw [ite_eq_left hlast]
    have hi : i = Fin.last l := Fin.ext hlast.1
    have hj : j = Fin.last l := Fin.ext hlast.2
    rw [hi, hj, shiftCore_one_last_diagonal hl]
  · rw [ite_eq_right hlast]
    by_cases hdeg : i.val+j.val = 2*l-1
    · rw [ite_eq_left hdeg]
      exact shiftCore_one_eq_one_of_add_eq i j hdeg
    · rw [ite_eq_right hdeg]
      have hi := i.isLt
      have hj := j.isLt
      exact shiftCore_one_eq_zero_of_add_lt i j (by omega)

#print axioms shiftCore_one_firstKnot_entries
#print axioms bilinearCoeff_shift_one
#print axioms shiftCore_one_eq_zero_of_add_lt
#print axioms shiftCore_one_eq_one_of_add_eq
#print axioms shiftCore_one_last_diagonal

end Nuttall
