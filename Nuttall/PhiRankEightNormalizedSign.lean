import Nuttall.MatrixQuadraticMargin
import Nuttall.PhiRankEightMainBlock
import Nuttall.PhiRankEightTailMatrix
import Mathlib.Tactic.Abel

namespace Nuttall

open scoped Matrix Matrix.Norms.Operator NNReal

theorem phiRankEightFirstTerm_signed_eq (p : ℕ) {X : ℝ} (hX : 0 < X) :
    phiRankEightTerm p X 1 * phiRankEightSign p = phiRankEightDominantBlock p X := by
  let J := phiRankEightSign p
  let S := phiRankEightShift p
  let T := S.transpose
  let P := phiRankEightCongruenceFactor p X
  let c := (Real.sqrt X)⁻¹
  have hJ : J*J = 1 := phiRankEightSign_mul_self p
  have hJt : J.transpose = J := by simp [J, phiRankEightSign]
  have hTmul : T*J = -(J*T) := by
    have ht := congrArg Matrix.transpose (phiRankEightSign_mul_shift p)
    change (J*S).transpose = (-(S*J)).transpose at ht
    simpa only [Matrix.transpose_mul, Matrix.transpose_neg, hJt, T] using ht
  have hJT : J*T*J = -T := by
    have hanti : J*T = -(T*J) := by rw [hTmul, neg_neg]
    rw [hanti, neg_mul, mul_assoc, hJ, mul_one]
  have hP : P = 1+c • S := rfl
  have hPt : P.transpose = 1+c • T := by
    rw [hP, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_smul]
  have hJP : J*P.transpose*J = 1-c • T := by
    rw [hPt]
    simp only [mul_add, add_mul, Matrix.mul_smul, Matrix.smul_mul, mul_one, hJ, hJT, smul_neg,
      sub_eq_add_neg]
  have hfirst : phiRankEightTerm p X 1 * J =
      (2*X) • (P*(1-c • T)) - (3:ℝ) • (1:Matrix (Fin p) (Fin p) ℝ) := by
    calc
      _ = (2*X) • (P*J*P.transpose*J) - (3:ℝ) • (J*J) := by
        simp only [phiRankEightTerm, phiRankEightGaussianMatrix_one, mul_one, one_smul,
          sub_mul, Matrix.smul_mul, P, J]
      _ = _ := by rw [hJ, mul_assoc P J P.transpose, mul_assoc P (J*P.transpose) J, hJP]
  have hprod : P*(1-c • T) = 1+c • (S-T)-(c*c) • (S*T) := by
    rw [hP]
    simp only [mul_sub, add_mul, Matrix.smul_mul, Matrix.mul_smul, mul_one, one_mul,
      smul_smul, smul_sub]
    abel
  have hc : Real.sqrt X*c = 1 := mul_inv_cancel₀ (Real.sqrt_pos.2 hX).ne'
  have hcX : X*c = Real.sqrt X := by
    calc
      _ = (Real.sqrt X*Real.sqrt X)*c := by rw [Real.mul_self_sqrt hX.le]
      _ = _ := by rw [mul_assoc, hc, mul_one]
  have hcc : X*(c*c) = 1 := by rw [← mul_assoc, hcX, hc]
  have hcx : (2*X)*c = 2*Real.sqrt X := by rw [mul_assoc, hcX]
  have hcXc : (2*X)*(c*c) = 2 := by rw [mul_assoc, hcc, mul_one]
  have hscaled : (2*X) • (1+c • (S-T)-(c*c) • (S*T)) - (3:ℝ) • 1 =
      (2*X-3) • (1:Matrix (Fin p) (Fin p) ℝ) + (2*Real.sqrt X) • (S-T) - (2:ℝ) • (S*T) := by
    simp only [smul_sub, smul_add, smul_smul, hcx, hcXc, sub_smul]
    abel
  change phiRankEightTerm p X 1 * J = _
  rw [hfirst, hprod, hscaled]
  have hST : S*T = Matrix.diagonal (fun i : Fin p => (i.val:ℝ)) :=
    phiRankEightShift_mul_transpose p
  rw [hST]
  ext i j
  by_cases hij : i = j <;>
    simp [phiRankEightDominantBlock, S, T, hij]

private theorem abs_entry_le_matrix_norm {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (i j : Fin p) :
    |A i j| ≤ ‖A‖ := by
  have hrow : ‖A i j‖₊ ≤ ∑ k : Fin p, ‖A i k‖₊ :=
    Finset.single_le_sum (f := fun k : Fin p => ‖A i k‖₊) (fun _ _ => zero_le) (Finset.mem_univ j)
  have hsup : ∑ k : Fin p, ‖A i k‖₊ ≤ Finset.univ.sup (fun a : Fin p => ∑ k : Fin p, ‖A a k‖₊) :=
    Finset.le_sup (f := fun a : Fin p => ∑ k : Fin p, ‖A a k‖₊) (Finset.mem_univ i)
  rw [← Real.norm_eq_abs, Matrix.linfty_opNorm_def]
  exact_mod_cast hrow.trans hsup

/-- The normalized tail matrix, with its sign diagonal applied, has positive determinant. -/
theorem phiRankEightNormalized_det_pos {p : ℕ} (hp₀ : 0 < p) (hp : p ≤ 8)
    {X : ℝ} (hX : 16 ≤ X) :
    0 < ((phiRankEightTerm p X 1 + ∑' k : ℕ, phiRankEightTerm p X (((k:ℝ)+2)^2)) *
      phiRankEightSign p).det := by
  let E := ∑' k : ℕ, phiRankEightTerm p X (((k:ℝ)+2)^2)
  let J := phiRankEightSign p
  have hE : ‖E‖ < 1/1000 := (phiRankEightTailMatrix_summable_norm_lt hp₀ hp hX).2
  change 0 < ((phiRankEightTerm p X 1 + E)*J).det
  rw [add_mul, show phiRankEightTerm p X 1 * J = phiRankEightDominantBlock p X from
    phiRankEightFirstTerm_signed_eq p (by linarith)]
  apply det_pos_of_quadratic_entry_margin _ _ (by norm_num : (0:ℝ) ≤ 1/1000)
    (phiRankEightDominantBlock_quadratic_le p X)
  · intro i j
    have he : |(E*J) i j| = |E i j| := by
      simp [J, phiRankEightSign, Matrix.mul_diagonal, abs_mul, abs_pow]
    rw [he]
    exact (abs_entry_le_matrix_norm E i j).trans hE.le
  · rw [Fintype.card_fin]
    have hp' : (p:ℝ) ≤ 8 := by exact_mod_cast hp
    have hsq := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ p) hp' 2
    linarith only [hX, hp', hsq]

#print axioms phiRankEightFirstTerm_signed_eq
#print axioms phiRankEightNormalized_det_pos

end Nuttall
