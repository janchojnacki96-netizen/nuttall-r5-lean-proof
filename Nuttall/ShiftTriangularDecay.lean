import Nuttall.ShiftOffCentral
import Nuttall.ShiftCorrection

namespace Nuttall

private theorem real_choose_pos {M i : ℕ} (hi : i ≤ M) :
    0 < (M.choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi

private theorem sqrt_choose_ratio_succ_le {M i : ℕ} (hi : i+1 ≤ M/2) :
    Real.sqrt ((M.choose i : ℝ)/(M.choose (i+1) : ℝ)) ≤
      Real.exp (-(1-2*((i:ℝ)+1)/((M:ℝ)+1))) := by
  let δ : ℝ := 1-2*((i:ℝ)+1)/((M:ℝ)+1)
  have hhalf : (2:ℝ)*((i:ℝ)+1) ≤ M := by
    exact_mod_cast (show 2*(i+1) ≤ M by omega)
  have hden : (0:ℝ) < (M:ℝ)+1 := by positivity
  have hδ₀ : 0 ≤ δ := by
    dsimp [δ]
    exact sub_nonneg.2 ((div_le_one hden).2 (by linarith only [hhalf]))
  have hδ₁ : δ ≤ 1 := by dsimp [δ]; exact sub_le_self _ (by positivity)
  have hM : i+1 ≤ M := by omega
  have hMi : (0:ℝ) < (M:ℝ)-i := sub_pos.2 (by exact_mod_cast (show i < M by omega))
  have hbin : (M.choose (i+1) : ℝ)*((i:ℝ)+1) = (M.choose i : ℝ)*((M:ℝ)-i) := by
    have h := congrArg (fun n : ℕ => (n:ℝ)) (Nat.choose_succ_right_eq M i)
    simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (show i ≤ M by omega)] using h
  have hr : (M.choose i : ℝ)/(M.choose (i+1) : ℝ) = ((i:ℝ)+1)/((M:ℝ)-i) := by
    apply (div_eq_div_iff (real_choose_pos hM).ne' hMi.ne').2
    linarith only [hbin]
  have hδ : (1-δ)/(1+δ) = ((i:ℝ)+1)/((M:ℝ)-i) := by
    have hδden : 1+δ ≠ 0 := by linarith
    apply (div_eq_div_iff hδden hMi.ne').2
    dsimp [δ]
    field_simp
    ring
  rw [hr, ← hδ]
  exact shiftScale_le_exp_neg hδ₀ hδ₁

/-- The sum of the adjacent exponents telescopes to a stronger bound
before the diagonal distance estimate is taken. -/
theorem sqrt_choose_ratio_le_exp_ramp {M i j : ℕ} (hji : j ≤ i) (hi : i ≤ M/2) :
    Real.sqrt ((M.choose j : ℝ)/(M.choose i : ℝ)) ≤
      Real.exp (-(((i:ℝ)-j)*((M:ℝ)-i-j))/((M:ℝ)+1)) := by
  induction i, hji using Nat.le_induction with
  | base =>
    rw [div_self (real_choose_pos (show j ≤ M by omega)).ne', Real.sqrt_one]
    simp
  | succ i hji ih =>
    have hi' : i ≤ M/2 := by omega
    have hp : 0 < (M.choose i : ℝ) := real_choose_pos (by omega)
    have hp' : 0 < (M.choose (i+1) : ℝ) := real_choose_pos (by omega)
    have hprod :
        Real.sqrt ((M.choose j : ℝ)/(M.choose (i+1) : ℝ)) =
          Real.sqrt ((M.choose j : ℝ)/(M.choose i : ℝ)) *
            Real.sqrt ((M.choose i : ℝ)/(M.choose (i+1) : ℝ)) := by
      rw [← Real.sqrt_mul (div_nonneg (Nat.cast_nonneg _) hp.le)]
      congr 1
      field_simp [hp.ne', hp'.ne']
    rw [hprod]
    calc
      _ ≤ Real.exp (-(((i:ℝ)-j)*((M:ℝ)-i-j))/((M:ℝ)+1)) *
          Real.exp (-(1-2*((i:ℝ)+1)/((M:ℝ)+1))) :=
        mul_le_mul (ih hi') (sqrt_choose_ratio_succ_le hi) (Real.sqrt_nonneg _) (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add, Nat.cast_succ]
        congr 1
        have hden : 0 < (M:ℝ)+1 := by positivity
        field_simp
        ring

/-- The triangular coefficients are bounded by a Gaussian in the distance
from the diagonal. -/
theorem shiftTriangular_entry_le_gaussian {M k : ℕ} (hM : 2*(k-1) ≤ M) (i j : Fin k) :
    shiftTriangular M k i j ≤ Real.exp (-((i.val:ℝ)-j.val)^2/((M:ℝ)+1)) := by
  by_cases hji : j ≤ i
  · have hji' : j.val ≤ i.val := hji
    have hihalf : i.val ≤ M/2 := by have := i.isLt; omega
    simp only [shiftTriangular, Matrix.of_apply, ite_eq_left hji]
    apply (sqrt_choose_ratio_le_exp_ramp hji' hihalf).trans
    apply Real.exp_le_exp.mpr
    have h₀ : 0 ≤ (i.val:ℝ)-j.val := sub_nonneg.2 (by exact_mod_cast hji')
    have h₁ : (i.val:ℝ)-j.val ≤ (M:ℝ)-i.val-j.val := by
      have h₂ : (2:ℝ)*i.val ≤ M := by exact_mod_cast (show 2*i.val ≤ M by omega)
      linarith
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left h₁ h₀]
  · simp [shiftTriangular, hji, Real.exp_nonneg]

theorem shiftCorrectionMatrix_diag {M k : ℕ} (hk : k ≤ M+1) (d : ℝ) (i : Fin k) :
    shiftCorrectionMatrix M k d i i = (1-d)/2 := by
  have hp : 0 < (M.choose i.val : ℝ) := real_choose_pos (by have := i.isLt; omega)
  simp only [shiftCorrectionMatrix, shiftTriangular, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.of_apply, ite_eq_left le_rfl, div_self hp.ne', Real.sqrt_one, Matrix.one_apply_eq,
    smul_eq_mul, mul_one]
  ring

theorem shiftCorrectionMatrix_off_diag {M k : ℕ} (d : ℝ) {i j : Fin k} (hij : i ≠ j) :
    shiftCorrectionMatrix M k d i j = shiftTriangular M k i j := by
  simp [shiftCorrectionMatrix, Matrix.one_apply_ne hij]

/-- The corrected triangular factor has nonnegative entries, with the diagonal
running from zero to one half. -/
theorem shiftCorrectionMatrix_entry_nonneg {M k : ℕ} (hk : k ≤ M+1) {d : ℝ}
    (hd : d ≤ 1) (i j : Fin k) : 0 ≤ shiftCorrectionMatrix M k d i j := by
  by_cases hij : i = j
  · subst j
    rw [shiftCorrectionMatrix_diag hk]
    linarith
  · simp only [shiftCorrectionMatrix, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne hij,
      smul_zero, sub_zero, shiftTriangular, Matrix.of_apply]
    split <;> positivity

#print axioms sqrt_choose_ratio_le_exp_ramp
#print axioms shiftTriangular_entry_le_gaussian
#print axioms shiftCorrectionMatrix_entry_nonneg

end Nuttall
