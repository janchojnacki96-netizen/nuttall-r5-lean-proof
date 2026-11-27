import Nuttall.ShiftCoreScaling
import Mathlib.Algebra.BigOperators.Field

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- Place the two factors in separate variables. -/
noncomputable def separatedProduct (P Q : ℝ[X]) : (ℝ[X])[X] :=
  P.map (C : ℝ →+* ℝ[X]) * C Q

theorem coeff_separatedProduct (P Q : ℝ[X]) (j l : ℕ) :
    ((separatedProduct P Q).coeff j).coeff l = P.coeff j * Q.coeff l := by
  simp only [separatedProduct, coeff_mul_C, coeff_map, coeff_C_mul]

theorem separatedProduct_mul (P Q R S : ℝ[X]) :
    separatedProduct (P*Q) (R*S) = separatedProduct P R * separatedProduct Q S := by
  simp only [separatedProduct, Polynomial.map_mul, map_mul]
  ring

theorem separatedProduct_pow (P Q : ℝ[X]) (M : ℕ) :
    separatedProduct (P^M) (Q^M) = (separatedProduct P Q)^M := by
  simp only [separatedProduct, Polynomial.map_pow, map_pow, mul_pow]

private theorem coeff_bilinear_one (M j l : ℕ) :
    bilinearCoeff M 1 0 0 1 j l = if j = l then (M.choose j : ℝ) else 0 := by
  unfold bilinearCoeff
  rw [coeff_bilinearPolynomial_pow]
  simp only [map_zero, map_one, zero_mul, add_zero, zero_add, one_mul, one_pow, mul_one, coeff_mul_C, coeff_X_pow]
  split <;> simp_all [eq_comm]

/-- The weighted sum of the two-variable products of the row polynomials
is the power of the degree-one orthogonality identity. -/
private theorem weighted_reflection_coeff_sum {c d : ℝ} (h : c^2+d^2=1)
    (M j l : ℕ) :
    let R (i : ℕ) := (C d + C (-c)*X)^i * (C c + C d*X)^(M-i)
    (∑ i ∈ Finset.range (M+1), (M.choose i : ℝ) * ((R i).coeff j * (R i).coeff l)) =
      if j = l then (M.choose j : ℝ) else 0 := by
  dsimp only
  let A : ℝ[X] := C c + C d*X
  let B : ℝ[X] := C d + C (-c)*X
  let R (i : ℕ) := B^i * A^(M-i)
  change (∑ i ∈ Finset.range (M+1), (M.choose i : ℝ) *
    ((R i).coeff j * (R i).coeff l)) = _
  let P := ∑ i ∈ Finset.range (M+1), C (C (M.choose i : ℝ)) * separatedProduct (R i) (R i)
  have hp : P = (separatedProduct B B + separatedProduct A A)^M := by
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro i _
    simp only [R, separatedProduct_mul, separatedProduct_pow, ← C_eq_natCast]
    ring
  have hsum : separatedProduct B B + separatedProduct A A = bilinearPolynomial 1 0 0 1 := by
    calc
      _ = C (C (c^2+d^2)) * (1 + (X : (ℝ[X])[X]) * C X) := by
        simp only [A, B, separatedProduct, Polynomial.map_add, Polynomial.map_mul,
          Polynomial.map_C, Polynomial.map_X, Polynomial.map_neg, map_add, map_mul, map_neg, map_pow]
        ring
      _ = _ := by
        rw [h]
        simp [bilinearPolynomial, ← C_mul_X_eq_monomial]
        ring
  have hcoeff := congrArg (fun Q : (ℝ[X])[X] => (Q.coeff j).coeff l) (hp.trans (by rw [hsum]))
  simp only [P, finsetSum_coeff, coeff_C_mul, coeff_separatedProduct] at hcoeff
  change _ = bilinearCoeff M 1 0 0 1 j l at hcoeff
  rwa [coeff_bilinear_one] at hcoeff

/-- The full coefficient matrix of the symmetric power is orthogonal in
the binomially normalized basis. Smaller leading blocks are restrictions of it. -/
theorem shiftReflectionPower_transpose_mul {d : ℝ} (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (M : ℕ) :
    (shiftReflectionPower M (M+1) d).transpose * shiftReflectionPower M (M+1) d = 1 := by
  let c := shiftCosine d
  let R (i : ℕ) := (C d + C (-c)*X)^i * (C c + C d*X)^(M-i)
  have hchoose (i : Fin (M+1)) : 0 < (M.choose i.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ i.isLt)
  ext j l
  let den := Real.sqrt (M.choose j.val : ℝ) * Real.sqrt (M.choose l.val : ℝ)
  have hden : den ≠ 0 := mul_ne_zero
    (Real.sqrt_pos.2 (hchoose j)).ne' (Real.sqrt_pos.2 (hchoose l)).ne'
  have hpair (i : Fin (M+1)) :
      shiftReflectionPower M (M+1) d i j * shiftReflectionPower M (M+1) d i l =
      ((M.choose i.val : ℝ) * ((R i.val).coeff j.val * (R i.val).coeff l.val)) / den := by
    simp only [shiftReflectionPower, Matrix.of_apply, bilinearCoeff, coeff_bilinearPolynomial_pow,
      coeff_mul_C]
    change ((R i.val).coeff j.val * M.choose i.val) /
        Real.sqrt ((M.choose i.val : ℝ) * M.choose j.val) *
        (((R i.val).coeff l.val * M.choose i.val) /
        Real.sqrt ((M.choose i.val : ℝ) * M.choose l.val)) = _
    rw [div_mul_div_comm, Real.sqrt_mul (hchoose i).le, Real.sqrt_mul (hchoose i).le]
    have hd : (Real.sqrt (M.choose i.val : ℝ) * Real.sqrt (M.choose j.val : ℝ)) *
        (Real.sqrt (M.choose i.val : ℝ) * Real.sqrt (M.choose l.val : ℝ)) =
        (M.choose i.val : ℝ) * den := by
      calc
        _ = (Real.sqrt (M.choose i.val : ℝ) * Real.sqrt (M.choose i.val : ℝ)) * den := by
          dsimp [den]
          ring
        _ = _ := by rw [Real.mul_self_sqrt (hchoose i).le]
    rw [hd]
    field_simp [(hchoose i).ne', hden]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hpair, ← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range (fun i => (M.choose i : ℝ) * ((R i).coeff j.val * (R i).coeff l.val))]
  rw [weighted_reflection_coeff_sum (shiftCosine_sq_add_sq hd₀ hd₁)]
  by_cases h : j = l
  · subst l
    rw [ite_eq_left rfl, Matrix.one_apply_eq, show den = (M.choose j.val : ℝ) from
      Real.mul_self_sqrt (hchoose j).le, div_self (hchoose j).ne']
  · have hv : j.val ≠ l.val := fun h' => h (Fin.ext h')
    simp [hv, Matrix.one_apply_ne h]

#print axioms shiftReflectionPower_transpose_mul

end Nuttall
