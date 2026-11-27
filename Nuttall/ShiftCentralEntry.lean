import Nuttall.ShiftCoreNorm
import Nuttall.ShiftCentralCoefficient
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Complex.Exponential

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

private theorem bicontent_mul_symm {P Q : (ℝ[X])[X]}
    (hP : ∀ i j, (P.coeff i).coeff j = (P.coeff j).coeff i)
    (hQ : ∀ i j, (Q.coeff i).coeff j = (Q.coeff j).coeff i) (i j : ℕ) :
    ((P*Q).coeff i).coeff j = ((P*Q).coeff j).coeff i := by
  simp only [coeff_mul, finsetSum_coeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [hP b.1 a.1, hQ b.2 a.2]

private theorem bilinearPolynomial_symm_coeff (a b e : ℝ) (i j : ℕ) :
    ((bilinearPolynomial a b b e).coeff i).coeff j =
      ((bilinearPolynomial a b b e).coeff j).coeff i := by
  by_cases hi₀ : i = 0 <;> by_cases hi₁ : i = 1 <;>
    by_cases hj₀ : j = 0 <;> by_cases hj₁ : j = 1 <;>
    simp_all [bilinearPolynomial, coeff_add, coeff_monomial, coeff_C, coeff_C_mul_X, coeff_X, eq_comm]

theorem bilinearCoeff_symm (M : ℕ) (a b e : ℝ) (i j : ℕ) :
    bilinearCoeff M a b b e i j = bilinearCoeff M a b b e j i := by
  induction M generalizing i j with
  | zero =>
    unfold bilinearCoeff
    simp only [pow_zero, coeff_one]
    split_ifs <;> simp_all [coeff_one]
  | succ M ih =>
    unfold bilinearCoeff at *
    simp only [pow_succ]
    exact bicontent_mul_symm ih (bilinearPolynomial_symm_coeff a b e) i j

theorem shiftReflectionPower_symm_entry (M k : ℕ) (d : ℝ) (i j : Fin k) :
    shiftReflectionPower M k d i j = shiftReflectionPower M k d j i := by
  simp only [shiftReflectionPower, Matrix.of_apply]
  rw [bilinearCoeff_symm M _ _ _ i.val j.val, mul_comm]

private theorem choose_monotone_to_half {M i j : ℕ} (hji : j ≤ i) (hi : i ≤ M/2) :
    M.choose j ≤ M.choose i := by
  induction i, hji using Nat.le_induction with
  | base => exact le_rfl
  | succ l _ ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem shiftReflectionPower_entry_formula {M k : ℕ} {d : ℝ} (hk : k ≤ M+1)
    (i j : Fin k) :
    shiftReflectionPower M k d j i =
      Real.sqrt ((M.choose j.val : ℝ)/(M.choose i.val : ℝ)) *
        (((C (shiftCosine d) + C d*X)^(M-j.val)) *
          (C d-C (shiftCosine d)*X)^j.val).coeff i.val := by
  have hi : 0 < (M.choose i.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (show i.val ≤ M by have := i.isLt; omega)
  have hj : 0 < (M.choose j.val : ℝ) := by
    exact_mod_cast Nat.choose_pos (show j.val ≤ M by have := j.isLt; omega)
  simp only [shiftReflectionPower, Matrix.of_apply, bilinearCoeff, coeff_bilinearPolynomial_pow,
    coeff_mul_C, map_neg, neg_mul, ← sub_eq_add_neg]
  rw [mul_comm ((C d-C (shiftCosine d)*X)^j.val), Real.sqrt_mul hj.le, Real.sqrt_div hj.le]
  have hs : (Real.sqrt (M.choose j.val : ℝ))^2 = (M.choose j.val : ℝ) := Real.sq_sqrt hj.le
  field_simp [(Real.sqrt_pos.2 hj).ne', (Real.sqrt_pos.2 hi).ne']
  rw [hs]

private theorem exp_small_mul_sqrt_pi_le_two : Real.exp (1/64:ℝ) * Real.sqrt Real.pi ≤ 2 := by
  have he : Real.exp (1/64:ℝ) ≤ 64/63 := by
    have h := Real.exp_bound_div_one_sub_of_interval (x := (1/64:ℝ)) (by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hp : Real.sqrt Real.pi ≤ 9/5 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · linarith [Real.pi_lt_d2]
  calc
    _ ≤ (64/63)*(9/5) := mul_le_mul he hp (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num

private theorem abs_shiftReflectionPower_entry_central_ordered {M k : ℕ} {d : ℝ}
    (hM : 0 < M) (hd : 0 < d) (hd₁ : d < 1) (hk : 2*(k-1) ≤ M)
    {i j : Fin k} (hji : j ≤ i)
    (hcenter : (M:ℝ)/2-j.val ≤ Real.sqrt M/16) :
    |shiftReflectionPower M k d j i| ≤ 2/(shiftCosine d*d*Real.sqrt M) := by
  let c := shiftCosine d
  have hc : 0 < c := by
    apply Real.sqrt_pos.2
    nlinarith [mul_pos (sub_pos.2 hd₁) (show 0 < 1+d by linarith)]
  have hi := i.isLt
  have hj := j.isLt
  have hihalf : i.val ≤ M/2 := by omega
  have hjhalf : j.val ≤ M/2 := (show j.val ≤ i.val from hji).trans hihalf
  have hchoose := choose_monotone_to_half (show j.val ≤ i.val from hji) hihalf
  have hden : (0:ℝ) < M.choose i.val := by exact_mod_cast Nat.choose_pos (show i.val ≤ M by omega)
  have hratio : Real.sqrt ((M.choose j.val : ℝ)/(M.choose i.val : ℝ)) ≤ 1 :=
    Real.sqrt_le_one.mpr ((div_le_one hden).2 (by exact_mod_cast hchoose))
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hβ : 0 ≤ (M:ℝ)/2-j.val := by
    have hh : 2*j.val ≤ M := by omega
    have hh' : (2:ℝ)*j.val ≤ M := by exact_mod_cast hh
    linarith
  have hexp : 4*((M:ℝ)/2-j.val)^2/(M:ℝ) ≤ 1/64 := by
    apply (div_le_iff₀ hMr).2
    have h := pow_le_pow_left₀ hβ hcenter 2
    have h2 : (Real.sqrt (M:ℝ)/16)^2 = (M:ℝ)/256 := by
      rw [div_pow, Real.sq_sqrt hMr.le]
      norm_num
    rw [h2] at h
    linarith
  let P : ℝ[X] := (C c + C d*X)^(M-j.val) * (C d-C c*X)^j.val
  have hmap : P.map Complex.ofRealHom =
      (C (c:ℂ)+C (d:ℂ)*X)^(M-j.val) * (C (d:ℂ)-C (c:ℂ)*X)^j.val := by
    simp [P, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_add, Polynomial.map_sub]
  have hcauchy := norm_central_shift_polynomialCoeff_le hM (show j.val ≤ M by omega)
    hc hd (shiftCosine_sq_add_sq hd.le hd₁.le) i.val
  rw [← hmap, coeff_map] at hcauchy
  have hp : |P.coeff i.val| ≤ Real.exp (4*((M:ℝ)/2-j.val)^2/M)*Real.sqrt Real.pi/(c*d*Real.sqrt M) := by
    simpa using hcauchy
  rw [shiftReflectionPower_entry_formula (by omega), abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  change Real.sqrt ((M.choose j.val : ℝ)/(M.choose i.val : ℝ))*|P.coeff i.val| ≤ _
  refine (mul_le_of_le_one_left (abs_nonneg _) hratio).trans (hp.trans ?_)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hexp) (Real.sqrt_nonneg _)).trans
    exp_small_mul_sqrt_pi_le_two

/-- The central bound with the binomial normalization, in either index order. -/
theorem abs_shiftReflectionPower_entry_central {M k : ℕ} {d : ℝ}
    (hM : 0 < M) (hd : 0 < d) (hd₁ : d < 1) (hk : 2*(k-1) ≤ M) (i j : Fin k)
    (hi : (M:ℝ)/2-i.val ≤ Real.sqrt M/16) (hj : (M:ℝ)/2-j.val ≤ Real.sqrt M/16) :
    |shiftReflectionPower M k d i j| ≤ 2/(shiftCosine d*d*Real.sqrt M) := by
  rcases le_total i j with h | h
  · exact abs_shiftReflectionPower_entry_central_ordered hM hd hd₁ hk h hi
  · rw [shiftReflectionPower_symm_entry]
    exact abs_shiftReflectionPower_entry_central_ordered hM hd hd₁ hk h hj

#print axioms bilinearCoeff_symm
#print axioms abs_shiftReflectionPower_entry_central

end Nuttall
