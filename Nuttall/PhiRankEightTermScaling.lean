import Nuttall.PhiRankEightGaussianScaling
import Nuttall.PhiRankEightTailMatrix

namespace Nuttall

open scoped BigOperators

private noncomputable def scaledEntries (p : ℕ) (X : ℝ) (f : ℕ → ℕ → ℝ) :
    Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => phiRankEightBasisScale X i.val * phiRankEightBasisScale X j.val * f i.val j.val

private theorem scaledEntries_transpose (p : ℕ) (X : ℝ) (f : ℕ → ℕ → ℝ) :
    (scaledEntries p X f).transpose = scaledEntries p X (fun i j => f j i) := by
  ext i j
  simp only [Matrix.transpose_apply, scaledEntries, Matrix.of_apply]
  rw [mul_comm (phiRankEightBasisScale X j.val)]

private theorem shift_mul_scaledEntries (p : ℕ) (X : ℝ) (f : ℕ → ℕ → ℝ) (i j : Fin p) :
    (phiRankEightShift p * scaledEntries p X f) i j =
      if i.val = 0 then 0 else
        Real.sqrt (i.val:ℝ) *
          (phiRankEightBasisScale X (i.val-1) * phiRankEightBasisScale X j.val * f (i.val-1) j.val) := by
  simp only [Matrix.mul_apply, phiRankEightShift, scaledEntries, Matrix.of_apply]
  by_cases hi : i.val = 0
  · simp [hi]
  · let k : Fin p := ⟨i.val-1, by have := i.isLt; omega⟩
    have hk : i.val = k.val+1 := by dsimp [k]; omega
    rw [ite_eq_right hi, Finset.sum_eq_single k]
    · rw [ite_eq_left hk]
    · intro a _ ha
      have hne : i.val ≠ a.val+1 := fun h => ha (Fin.ext (by omega))
      simp [hne]
    · simp

private theorem factor_mul_scaledEntries (p : ℕ) (X : ℝ) (f : ℕ → ℕ → ℝ) :
    phiRankEightCongruenceFactor p X * scaledEntries p X f =
      scaledEntries p X (fun i j => f i j + if i = 0 then 0 else f (i-1) j) := by
  ext i j
  simp only [phiRankEightCongruenceFactor, add_mul, one_mul, Matrix.smul_mul, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, shift_mul_scaledEntries]
  simp only [scaledEntries, Matrix.of_apply]
  by_cases hi : i.val = 0
  · simp [hi]
  · simp only [ite_eq_right hi]
    have hi' : i.val-1+1 = i.val := by omega
    have h := phiRankEightBasisScale_succ X (i.val-1)
    rw [hi'] at h
    rw [show (Real.sqrt X)⁻¹ * (Real.sqrt (i.val:ℝ) *
        (phiRankEightBasisScale X (i.val-1)*phiRankEightBasisScale X j.val*f (i.val-1) j.val)) =
        (Real.sqrt (i.val:ℝ)/Real.sqrt X*phiRankEightBasisScale X (i.val-1))*
          phiRankEightBasisScale X j.val * f (i.val-1) j.val by ring, h]
    ring

private theorem scaledEntries_mul_factor_transpose (p : ℕ) (X : ℝ) (f : ℕ → ℕ → ℝ) :
    scaledEntries p X f * (phiRankEightCongruenceFactor p X).transpose =
      scaledEntries p X (fun i j => f i j + if j = 0 then 0 else f i (j-1)) := by
  have h := congrArg Matrix.transpose (factor_mul_scaledEntries p X (fun i j => f j i))
  simpa only [Matrix.transpose_mul, scaledEntries_transpose] using h

theorem phiRankEightTerm_eq_scaled_compact (p : ℕ) {X : ℝ} (hX : 0 < X) (q : ℝ)
    (i j : Fin p) :
    phiRankEightTerm p X q i j =
      (phiRankEightBasisScale X i.val * phiRankEightBasisScale X j.val) *
        phiCompactPolynomial X q i.val j.val * Real.exp (-(q-1)*X) := by
  have hg : phiRankEightGaussianMatrix p X q =
      scaledEntries p X (fun a b => phiCompactGaussian X q a b * Real.exp (-(q-1)*X)) := by
    ext a b
    simp only [phiRankEightGaussianMatrix, scaledEntries, Matrix.of_apply,
      phiRankEightGaussian_eq_scaled_compact hX, mul_assoc]
  unfold phiRankEightTerm
  rw [hg, factor_mul_scaledEntries, scaledEntries_mul_factor_transpose]
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, scaledEntries, Matrix.of_apply,
    phiCompactPolynomial]
  by_cases hi : i.val = 0 <;> by_cases hj : j.val = 0 <;> simp [hi, hj] <;> ring

#print axioms phiRankEightTerm_eq_scaled_compact

end Nuttall
