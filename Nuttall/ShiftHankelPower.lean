import Nuttall.ShiftHankelBasis

namespace Nuttall

open Polynomial
open scoped Polynomial BigOperators

/-- The uncropped generating polynomial before dividing by the exponential parameter. -/
private noncomputable def hankelForm (u s : ℝ) : (ℝ[X])[X] :=
  C (C u) * X * (1-C X) + C (C u) * C X * (1-X) + C (C s) * (1-X) * (1-C X)

private theorem hankelForm_eq_shift (u d : ℝ) :
    hankelForm u (u*(1-d)) = C (C u) * bilinearPolynomial (1-d) d d (-(1+d)) := by
  unfold hankelForm
  rw [bilinearPolynomial_shift]
  simp only [map_sub, map_mul, map_one]
  ring

private theorem trinomial_pow {R : Type*} [CommSemiring R] (A B D : R) (M : ℕ) :
    (A+B+D)^M =
      ∑ a ∈ Finset.range (M+1), ∑ b ∈ Finset.range (M-a+1),
        A^a * B^b * D^(M-a-b) * (M.choose a : R) * ((M-a).choose b : R) := by
  rw [add_assoc, add_pow]
  apply Finset.sum_congr rfl
  intro a _
  rw [add_pow, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  ac_rfl

private theorem trinomial_factorial {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M-a) :
    (M.choose a : ℝ) * ((M-a).choose b : ℝ) =
      (M.factorial : ℝ) / (a.factorial : ℝ) / (b.factorial : ℝ) / ((M-a-b).factorial : ℝ) := by
  have h₁ : (M.choose a : ℝ) * a.factorial * (M-a).factorial = M.factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial ha
  have h₂ : ((M-a).choose b : ℝ) * b.factorial * (M-a-b).factorial = (M-a).factorial := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hb
  rw [← h₁, ← h₂]
  field_simp

private theorem hankelForm_pow (M : ℕ) (u s : ℝ) :
    (hankelForm u s)^M =
      ∑ a ∈ Finset.range (M+1), ∑ b ∈ Finset.range (M-a+1),
        C (C ((M.factorial : ℝ) * (s^(M-a-b) / ((M-a-b).factorial : ℝ)))) *
          separatedProduct (shiftHankelBasisTerm M a u) (shiftHankelBasisTerm M b u) := by
  unfold hankelForm
  rw [trinomial_pow]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  have ha' : a ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp ha)
  have hb' : b ≤ M-a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
  have hpow₁ : b+(M-a-b) = M-a := by omega
  have hpow₂ : a+(M-a-b) = M-b := by omega
  have hscalar : (u^a : ℝ) * u^b * s^(M-a-b) * (M.choose a : ℝ) * ((M-a).choose b : ℝ) =
      (M.factorial : ℝ) * (s^(M-a-b) / ((M-a-b).factorial : ℝ)) *
        (u^a / (a.factorial : ℝ)) * (u^b / (b.factorial : ℝ)) := by
    rw [mul_assoc (u^a * u^b * s^(M-a-b)), trinomial_factorial ha' hb']
    ring
  simp only [shiftHankelBasisTerm, separatedProduct, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_one,
    map_mul, map_pow, map_sub, map_one, ← C_eq_natCast]
  have hleft :
      (C (C u) * (X : (ℝ[X])[X]) * (1-C X))^a *
        (C (C u) * C X * (1-X))^b *
        (C (C s) * (1-X) * (1-C X))^(M-a-b) *
        C (C (M.choose a : ℝ)) * C (C ((M-a).choose b : ℝ)) =
        C (C ((u^a : ℝ) * u^b * s^(M-a-b) * (M.choose a : ℝ) * ((M-a).choose b : ℝ))) *
          (X^a * (C X)^b * ((1-X)^b * (1-X)^(M-a-b)) * ((1-C X)^a * (1-C X)^(M-a-b))) := by
    simp only [map_mul, map_pow, mul_pow]
    ring
  rw [hleft, hscalar, ← pow_add, ← pow_add, hpow₁, hpow₂]
  simp only [map_mul]
  ring

/-- The positive Hankel term of a single translated theta summand. -/
noncomputable def hankelPowerMatrix (M k : ℕ) (s : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun a b => s^(M-(a.val+b.val)) / ((M-(a.val+b.val)).factorial : ℝ)

private theorem hankelForm_pow_coeff_cropped {M k : ℕ} (hk : 2*(k-1) ≤ M)
    (u s : ℝ) (i j : Fin k) :
    (((hankelForm u s)^M).coeff i.val).coeff j.val =
      (M.factorial : ℝ) * ((shiftHankelPolynomial M k u (hankelPowerMatrix M k s)).coeff i.val).coeff j.val := by
  have hi := i.isLt
  have hj := j.isLt
  have hk' : k ≤ M+1 := by omega
  rw [hankelForm_pow]
  simp only [shiftHankelPolynomial, finsetSum_coeff, coeff_C_mul, coeff_separatedProduct,
    hankelPowerMatrix, Matrix.of_apply, Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin k,
    (M.factorial : ℝ) * (s^(M-(a+b.val)) / ((M-(a+b.val)).factorial : ℝ) *
      ((shiftHankelBasisTerm M a u).coeff i.val * (shiftHankelBasisTerm M b.val u).coeff j.val)))]
  rw [← Finset.sum_subset (Finset.range_mono hk')]
  · apply Finset.sum_congr rfl
    intro a ha
    have ha' := Finset.mem_range.mp ha
    rw [← Finset.sum_subset (Finset.range_mono (show k ≤ M-a+1 by omega))]
    · rw [Fin.sum_univ_eq_sum_range (fun b =>
        (M.factorial : ℝ) * (s^(M-(a+b)) / ((M-(a+b)).factorial : ℝ) *
          ((shiftHankelBasisTerm M a u).coeff i.val * (shiftHankelBasisTerm M b u).coeff j.val)))]
      apply Finset.sum_congr rfl
      intro b _
      rw [show M-a-b = M-(a+b) by omega]
      ring
    · intro b _ hbn
      have hb' := Nat.le_of_not_lt (fun h => hbn (Finset.mem_range.mpr h))
      rw [shiftHankelBasisTerm_coeff_eq_zero _ (hj.trans_le hb')]
      ring
  · intro a _ han
    have ha' := Nat.le_of_not_lt (fun h => han (Finset.mem_range.mpr h))
    simp [shiftHankelBasisTerm_coeff_eq_zero _ (hi.trans_le ha')]

/-- The power-(M) generating transformation agrees on the complete (k)-by-(k) block. -/
theorem hankelPowerMatrix_coeff {M k : ℕ} (hk : 2*(k-1) ≤ M)
    (u d : ℝ) (i j : Fin k) :
    ((shiftHankelPolynomial M k u (hankelPowerMatrix M k (u*(1-d)))).coeff i.val).coeff j.val =
      (u^M / (M.factorial : ℝ)) *
        bilinearCoeff M (1-d) d d (-(1+d)) i.val j.val := by
  have h := hankelForm_pow_coeff_cropped hk u (u*(1-d)) i j
  simp only [hankelForm_eq_shift, mul_pow, ← map_pow, coeff_C_mul] at h
  field_simp
  unfold bilinearCoeff
  linarith only [h]

#print axioms hankelPowerMatrix_coeff

end Nuttall
