import Nuttall.ShiftCentralEntry
import Nuttall.ShiftOffCentral
import Nuttall.ShiftMatrixEnvelope

namespace Nuttall

open scoped BigOperators Matrix.Norms.L2Operator

/-- The sharp shift estimate in equation eq:shift of Section 4.2. -/
theorem norm_shiftCore_le_eq_shift {M k : ℕ} {d : ℝ}
    (hM : 0 < M) (hd : 0 < d) (hd₁ : d < 1) (hk : 2*(k-1) ≤ M) :
    ‖shiftCore M k d‖ ≤
      2/((1-(shiftScale d)^2)*shiftCosine d*d*Real.sqrt M) +
        (k:ℝ)*Real.exp (-d*Real.sqrt M/16) := by
  classical
  let s := shiftScale d
  let c := shiftCosine d
  let v (i : Fin k) := s^(k-1-i.val)
  let b := 2/(c*d*Real.sqrt M)
  let e := Real.exp (-d*Real.sqrt M/16)
  let central (i : Fin k) := (M:ℝ)/2-i.val ≤ Real.sqrt M/16
  let A : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun i j => if central i ∧ central j then shiftCore M k d i j else 0
  let B : Matrix (Fin k) (Fin k) ℝ :=
    Matrix.of fun i j => if central i ∧ central j then 0 else shiftCore M k d i j
  have hs : 0 ≤ s := (shiftScale_pos hd.le hd₁).le
  have hs₁ : s < 1 := (shiftScale_le_exp_neg hd.le hd₁.le).trans_lt
    (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd))
  have hc : 0 < c := by
    apply Real.sqrt_pos.2
    nlinarith [mul_pos (sub_pos.2 hd₁) (show 0 < 1+d by linarith)]
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hv (i : Fin k) : 0 ≤ v i := pow_nonneg hs _
  have he : 0 ≤ e := Real.exp_nonneg _
  have hsum : shiftCore M k d = A+B := by
    ext i j
    by_cases h : central i ∧ central j <;> simp [A, B, h]
  have hA : ‖A‖ ≤ b * ∑ i, (v i)^2 := by
    apply norm_matrix_le_of_entry_envelope A v hb
    intro i j
    by_cases h : central i ∧ central j
    · have ht := abs_shiftReflectionPower_entry_central hM hd hd₁ hk i j h.1 h.2
      have hpow : M-(i.val+j.val) = (M-2*(k-1))+(k-1-i.val)+(k-1-j.val) := by
        have := i.isLt
        have := j.isLt
        omega
      simp only [A, Matrix.of_apply, ite_eq_left h, shiftCore_eq_scaled_reflectionPower hd.le hd₁ hk,
        abs_mul]
      rw [abs_of_nonneg (show 0 ≤ (shiftScale d)^(M-(i.val+j.val)) from pow_nonneg hs _)]
      change s^(M-(i.val+j.val)) * |shiftReflectionPower M k d i j| ≤ b*v i*v j
      rw [hpow, pow_add, pow_add]
      change s^(M-2*(k-1))*v i*v j * |shiftReflectionPower M k d i j| ≤ _
      calc
        _ ≤ s^(M-2*(k-1))*v i*v j * b :=
          mul_le_mul_of_nonneg_left ht (mul_nonneg (mul_nonneg (pow_nonneg hs _) (hv i)) (hv j))
        _ = s^(M-2*(k-1))*(b*v i*v j) := by ring
        _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (mul_nonneg hb (hv i)) (hv j))
          (pow_le_one₀ hs hs₁.le)
    · simp only [A, Matrix.of_apply, ite_eq_right h, abs_zero]
      exact mul_nonneg (mul_nonneg hb (hv i)) (hv j)
  have hB : ‖B‖ ≤ (k:ℝ)*e := by
    have h := norm_matrix_le_of_entry_envelope B (fun _ => 1) he (fun i j => by
      simp only [mul_one]
      by_cases h : central i ∧ central j
      · simpa [B, h] using he
      · have hoff : Real.sqrt (M:ℝ)/16 ≤ (M:ℝ)/2-i.val ∨
              Real.sqrt (M:ℝ)/16 ≤ (M:ℝ)/2-j.val := by
          rcases not_and_or.mp h with h' | h'
          · exact Or.inl (le_of_lt (not_le.mp h'))
          · exact Or.inr (le_of_lt (not_le.mp h'))
        simpa only [B, Matrix.of_apply, ite_eq_right h] using
          abs_shiftCore_le_offCentral hd.le hd₁ hk i j hoff)
    simpa [mul_comm] using h
  have hgeo := shift_geometricWeight_sum_le k hs hs₁
  rw [hsum]
  calc
    _ ≤ ‖A‖+‖B‖ := norm_add_le _ _
    _ ≤ b*(1/(1-s^2))+(k:ℝ)*e :=
      add_le_add (hA.trans (mul_le_mul_of_nonneg_left hgeo hb)) hB
    _ = _ := by
      change (2/(c*d*Real.sqrt M))*(1/(1-s^2))+(k:ℝ)*e =
        2/((1-s^2)*c*d*Real.sqrt M)+(k:ℝ)*e
      rw [div_mul_div_comm, mul_one, show (c*d*Real.sqrt M)*(1-s^2) =
        (1-s^2)*c*d*Real.sqrt M by ring]

#print axioms norm_shiftCore_le_eq_shift

end Nuttall
