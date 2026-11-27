import Nuttall.ShiftReflectionOrthogonality
import Mathlib.Analysis.CStarAlgebra.Matrix

namespace Nuttall

open scoped Matrix.Norms.L2Operator

private theorem norm_matrix_one_le {n : Type*} [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℝ)‖ ≤ 1 := by
  rw [← Matrix.diagonal_one, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun _ => by simp)

private theorem norm_matrix_le_one_of_transpose_mul {m n : Type*}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (A : Matrix m n ℝ) (h : A.transpose * A = 1) : ‖A‖ ≤ 1 := by
  have hn := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, h] at hn
  nlinarith only [hn, norm_matrix_one_le (n := n), norm_nonneg A, sq_nonneg (‖A‖-1)]

/-- Restricting an operator to the same subset of input and output coordinates
does not enlarge the Euclidean operator norm. -/
private theorem norm_submatrix_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix n n ℝ) (f : m ↪ n) :
    ‖A.submatrix f f‖ ≤ ‖A‖ := by
  let E := (1 : Matrix n n ℝ).submatrix id f
  have ht : E.transpose = (1 : Matrix n n ℝ).submatrix f id := by
    ext i j
    simp [E, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.one_apply, eq_comm]
  have hleft (B : Matrix n n ℝ) : E.transpose * B = B.submatrix f id := by
    rw [ht]
    exact Matrix.one_submatrix_mul f (Equiv.refl n) B
  have hright (B : Matrix m n ℝ) : B * E = B.submatrix id f :=
    Matrix.mul_submatrix_one (Equiv.refl n) f B
  have hE : E.transpose * E = 1 := by
    calc
      E.transpose * E = (E.transpose * (1 : Matrix n n ℝ)) * E := by rw [Matrix.mul_one]
      _ = ((1 : Matrix n n ℝ).submatrix f id).submatrix id f := by rw [hright, hleft]
      _ = 1 := by
        ext i j
        simp [Matrix.submatrix_apply, Matrix.one_apply, f.injective.eq_iff]
  have he := norm_matrix_le_one_of_transpose_mul E hE
  have het : ‖E.transpose‖ ≤ 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]
    exact he
  calc
    ‖A.submatrix f f‖ = ‖(E.transpose * A) * E‖ := by
      rw [hright, hleft]
      rfl
    _ ≤ ‖E.transpose * A‖ * ‖E‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖E.transpose * A‖ := mul_le_of_le_one_right (norm_nonneg _) he
    _ ≤ ‖E.transpose‖ * ‖A‖ := Matrix.l2_opNorm_mul _ _
    _ ≤ ‖A‖ := mul_le_of_le_one_left (norm_nonneg _) het

/-- A leading block of the orthogonal symmetric power is contractive. -/
theorem norm_shiftReflectionPower_le_one {M k : ℕ} {d : ℝ}
    (hk : k ≤ M+1) (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) :
    ‖shiftReflectionPower M k d‖ ≤ 1 := by
  let f : Fin k ↪ Fin (M+1) := ⟨Fin.castLE hk, Fin.castLE_injective hk⟩
  have hf : shiftReflectionPower M k d = (shiftReflectionPower M (M+1) d).submatrix f f := rfl
  rw [hf]
  exact (norm_submatrix_le _ f).trans
    (norm_matrix_le_one_of_transpose_mul _ (shiftReflectionPower_transpose_mul hd₀ hd₁ M))

/-- The two diagonal weights leave a residual power after restricting to
the first (k) coordinates of the symmetric power. -/
theorem shiftCore_eq_diagonal_mul {M k : ℕ} {d : ℝ}
    (hd₀ : 0 ≤ d) (hd₁ : d < 1) (hM : 2*(k-1) ≤ M) :
    let D := Matrix.diagonal fun i : Fin k => shiftScale d ^ (k-1-i.val)
    shiftCore M k d =
      (shiftScale d ^ (M-2*(k-1))) • (D * shiftReflectionPower M k d * D) := by
  dsimp only
  ext i j
  rw [shiftCore_eq_scaled_reflectionPower hd₀ hd₁ hM, Matrix.smul_apply,
    Matrix.mul_diagonal, Matrix.diagonal_mul, smul_eq_mul]
  have hi := i.isLt
  have hj := j.isLt
  have he : M-(i.val+j.val) = (M-2*(k-1))+(k-1-i.val)+(k-1-j.val) := by omega
  rw [he, pow_add, pow_add]
  ring

/-- The operator-norm bound which keeps the residual exponent, including its
vanishing in the critical block. The estimate uses (d<1) as in the active sums. -/
theorem norm_shiftCore_le_pow {M k : ℕ} {d : ℝ}
    (hd₀ : 0 ≤ d) (hd₁ : d < 1) (hM : 2*(k-1) ≤ M) :
    ‖shiftCore M k d‖ ≤ shiftScale d ^ (M-2*(k-1)) := by
  let s := shiftScale d
  let D := Matrix.diagonal fun i : Fin k => s ^ (k-1-i.val)
  have hs : 0 ≤ s := (shiftScale_pos hd₀ hd₁).le
  have hs' : s ≤ 1 := by
    apply Real.sqrt_le_one.mpr
    have hd : 0 < 1+d := by linarith
    exact (div_le_one hd).2 (by linarith)
  have hD : ‖D‖ ≤ 1 := by
    change ‖Matrix.diagonal (fun i : Fin k => s^(k-1-i.val))‖ ≤ 1
    rw [Matrix.l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    rw [Real.norm_of_nonneg (pow_nonneg hs _)]
    exact pow_le_one₀ hs hs'
  have hk : k ≤ M+1 := by omega
  have hT := norm_shiftReflectionPower_le_one hk hd₀ hd₁.le
  have hDT : ‖D * shiftReflectionPower M k d‖ ≤ 1 :=
    (Matrix.l2_opNorm_mul _ _).trans
      (mul_le_of_le_one_right (norm_nonneg _) hT |>.trans hD)
  rw [shiftCore_eq_diagonal_mul hd₀ hd₁ hM, norm_smul, Real.norm_of_nonneg (pow_nonneg hs _)]
  change s^(M-2*(k-1)) * ‖D * shiftReflectionPower M k d * D‖ ≤ _
  apply mul_le_of_le_one_right (pow_nonneg hs _)
  exact (Matrix.l2_opNorm_mul _ _).trans
    (mul_le_of_le_one_right (norm_nonneg _) hD |>.trans hDT)

private theorem continuous_shiftCore (M k : ℕ) : Continuous (shiftCore M k) := by
  let P (d : ℝ) := bilinearPolynomial (1-d) d d (-(1+d))
  have hP (i j : ℕ) : Continuous fun d => ((P d).coeff i).coeff j := by
    simp only [P, bilinearPolynomial, Polynomial.coeff_add,
      Polynomial.coeff_monomial, Polynomial.coeff_C]
    split_ifs <;> simp only [Polynomial.coeff_add, Polynomial.coeff_C,
      Polynomial.coeff_C_mul_X, Polynomial.coeff_zero] <;> (try split_ifs) <;> fun_prop
  have hpow (i j : ℕ) : Continuous fun d => (((P d)^M).coeff i).coeff j := by
    induction M generalizing i j with
    | zero => simpa only [pow_zero] using continuous_const
    | succ M ih =>
      simp only [pow_succ, Polynomial.coeff_mul, Polynomial.finsetSum_coeff]
      apply continuous_finsetSum _ (fun a _ => ?_)
      exact continuous_finsetSum _ (fun b _ =>
        (ih a.1 b.1).mul (hP a.2 b.2))
  apply continuous_matrix
  intro i j
  exact (hpow i.val j.val).div_const _

/-- The contraction bound extends to (d=1), where the diagonal scaling degenerates. -/
theorem norm_shiftCore_le_one {M k : ℕ} {d : ℝ}
    (hd₀ : 0 ≤ d) (hd₁ : d ≤ 1) (hM : 2*(k-1) ≤ M) :
    ‖shiftCore M k d‖ ≤ 1 := by
  have hclosed : IsClosed {x : ℝ | ‖shiftCore M k x‖ ≤ 1} :=
    isClosed_le (continuous_shiftCore M k).norm continuous_const
  have hsub : Set.Ico (0 : ℝ) 1 ⊆ {x : ℝ | ‖shiftCore M k x‖ ≤ 1} := by
    intro x hx
    exact (norm_shiftCore_le_pow hx.1 hx.2 hM).trans
      (pow_le_one₀ (shiftScale_pos hx.1 hx.2).le
        (Real.sqrt_le_one.mpr ((div_le_one (by linarith [hx.1])).2 (by linarith [hx.1]))))
  apply hclosed.closure_subset_iff.mpr hsub
  rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1)]
  exact ⟨hd₀, hd₁⟩

#print axioms norm_shiftReflectionPower_le_one
#print axioms shiftCore_eq_diagonal_mul
#print axioms norm_shiftCore_le_pow
#print axioms norm_shiftCore_le_one

end Nuttall
