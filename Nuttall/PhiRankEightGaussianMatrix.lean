import Nuttall.PhiRankEightGaussianRows
import Mathlib.Analysis.Matrix.Normed

namespace Nuttall

open scoped Matrix.Norms.Operator NNReal

/-- Leading block of the normalized Gaussian coefficient matrix. -/
noncomputable def phiRankEightGaussianMatrix (p : ℕ) (X q : ℝ) : Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j => phiRankEightGaussian X q i.val j.val

theorem phiRankEightGaussianMatrix_norm_le {p : ℕ} (hp : p ≤ 8) {X q : ℝ}
    (hX : 16 ≤ X) (hq : 4 ≤ q) :
    ‖phiRankEightGaussianMatrix p X q‖ ≤
      2^46*(X/16)^7*(q/4)^14*Real.exp (-(q-1)*X) := by
  let bound : ℝ≥0 := ⟨2^46*(X/16)^7*(q/4)^14*Real.exp (-(q-1)*X), by positivity⟩
  rw [Matrix.linfty_opNorm_def]
  change ((Finset.univ.sup fun i : Fin p => ∑ j : Fin p, ‖phiRankEightGaussian X q i.val j.val‖₊ :
    ℝ≥0):ℝ) ≤ (bound:ℝ)
  rw [NNReal.coe_le_coe]
  apply Finset.sup_le
  intro i _
  apply NNReal.coe_le_coe.mp
  push_cast
  simp only [Real.norm_eq_abs, bound]
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => |phiRankEightGaussian X q i.val j|)]
  apply (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp) (fun j _ _ => abs_nonneg _)).trans
  have h := phiRankEightGaussian_row_le hX hq (i.castLE hp)
  simp only [Fin.val_castLE] at h
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => |phiRankEightGaussian X q i.val j|)] at h
  exact h

#print axioms phiRankEightGaussianMatrix_norm_le

end Nuttall
