import Nuttall.PhiCompactTransfer
import Nuttall.PhiCompactTailBound
import Nuttall.MatrixRowMargin

namespace Nuttall

open scoped BigOperators

private noncomputable def phiFarLeft (X : ℝ) (i : ℕ) : ℝ :=
  (i.factorial:ℝ)*3^i/X^i

private noncomputable def phiFarRight (j : ℕ) : ℝ := (-1:ℝ)^j/3^j

private def phiFarDiag (X : ℝ) (i : ℕ) : ℝ := 2*X-3-2*i

private noncomputable def phiFarShape (X : ℝ) (i j : ℕ) : ℝ :=
  if i = j then phiFarDiag X i
  else if i = j+1 then 6*i else if j = i+1 then -2*X/3 else 0

set_option maxHeartbeats 1500000 in
private theorem phiFarMain_eq_shape {X : ℝ} (hX₀ : X ≠ 0) (i j : Fin 4) :
    phiFarLeft X i.val * phiCompactPolynomial X 1 i.val j.val * phiFarRight j.val =
      phiFarShape X i.val j.val := by
  fin_cases i <;> fin_cases j <;>
    norm_num [phiFarLeft, phiFarRight, phiCompactPolynomial, phiCompactGaussian,
      phiFarShape, phiFarDiag, Finset.sum_range_succ, Nat.factorial] <;>
    field_simp [hX₀] <;> ring

private theorem phiFarShape_row_bound {X : ℝ} (hX : 16 ≤ X) (i : Fin 4) :
    (∑ j ∈ Finset.range 4, |phiFarShape X i.val j - if i.val = j then phiFarDiag X i.val else 0|)
      ≤ 2*X/3+12 := by
  have hnonpos : -(2*X/3) ≤ 0 := by linarith
  fin_cases i <;>
    norm_num [Finset.sum_range_succ, phiFarShape, phiFarDiag, neg_mul, neg_div, hnonpos,
      abs_of_nonneg, abs_of_nonpos] <;> linarith

private theorem phiFarLeft_bounds {X : ℝ} (hX : 16 ≤ X) {i : ℕ} (hi : i < 4) :
    0 < phiFarLeft X i ∧ phiFarLeft X i ≤ 162 := by
  have hX₀ : 0 < X := by linarith
  have hf : (i.factorial:ℝ) ≤ 6 := by interval_cases i <;> norm_num [Nat.factorial]
  have hp : (3:ℝ)^i ≤ 27 := by interval_cases i <;> norm_num
  have hd : 1 ≤ X^i := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by linarith : 1 ≤ X) i
  exact ⟨by unfold phiFarLeft; positivity, (div_le_self (by positivity) hd).trans
    (by nlinarith only [mul_le_mul hf hp (by positivity) (by norm_num : (0:ℝ) ≤ 6)])⟩

/-- Tail sign via an asymmetric diagonal rescaling and strict row sums.
This only uses the 4×4 block, so no complex Gaussian norm estimate is needed. -/
theorem phiFarWronskian_pos {p : ℕ} (hp : p ≤ 4) (t : ℝ)
    (hX : 16 ≤ phiThetaCoordinate t) :
    0 < kernelMinorSign p * wronskian W5.Phi p t := by
  let X := phiThetaCoordinate t
  have hX₀ : 0 < X := by linarith [hX]
  let A : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.diagonal (fun i => phiFarLeft X i.val) * phiCompactMatrix p X *
      Matrix.diagonal (fun j => phiFarRight j.val)
  let d (i : Fin p) := phiFarDiag X i.val
  have hd (i : Fin p) : 2*X-9 ≤ d i := by
    have hi : (i.val:ℝ) ≤ 3 := by exact_mod_cast (show i.val ≤ 3 by omega)
    unfold d phiFarDiag
    linarith
  have hrow (i : Fin p) : (∑ j : Fin p, |A i j - Matrix.diagonal d i j|) < d i := by
    have hi : i.val < 4 := i.isLt.trans_le hp
    have hs (j : Fin p) :
        |A i j - Matrix.diagonal d i j| ≤
          |phiFarShape X i.val j.val - Matrix.diagonal d i j| + 162/10000 := by
      have hj := j.isLt.trans_le hp
      let R := ∑' k, phiCompactTerm X i.val j.val (2+k)
      have hR : |R| ≤ (1:ℝ)/10000 := phiCompactFarTail_abs_le hX hi hj
      have hF : phiCompactMatrix p X i j = phiCompactPolynomial X 1 i.val j.val + R := by
        simp only [phiCompactMatrix, Matrix.of_apply, X]
        rw [← (phiCompactTerm_summable t hi hj).sum_add_tsum_nat_add 2]
        simp [R, Finset.sum_range_succ, phiCompactTerm, phiCompactPolynomial, X, add_comm]
      have he : A i j = phiFarShape X i.val j.val + phiFarLeft X i.val * R * phiFarRight j.val := by
        simp only [A, Matrix.diagonal_mul, Matrix.mul_diagonal, hF, mul_add, add_mul]
        rw [phiFarMain_eq_shape hX₀.ne' ⟨i.val,hi⟩ ⟨j.val,hj⟩]
      have hb : |phiFarRight j.val| ≤ 1 := by
        unfold phiFarRight
        simp only [abs_div, abs_pow, abs_neg, abs_one, abs_of_nonneg (by positivity : 0 ≤ (3:ℝ)^j.val)]
        have h := one_div_le_one_div_of_le zero_lt_one (show (1:ℝ) ≤ 3^j.val from by
          simpa only [one_pow] using
            pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) (by norm_num : (1:ℝ) ≤ 3) j.val)
        simpa only [one_pow, div_one] using h
      rw [he, show phiFarShape X i.val j.val + phiFarLeft X i.val * R * phiFarRight j.val -
          Matrix.diagonal d i j =
          (phiFarShape X i.val j.val - Matrix.diagonal d i j) +
          phiFarLeft X i.val * R * phiFarRight j.val by ring]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      have hL := phiFarLeft_bounds hX hi
      rw [abs_mul, abs_mul, abs_of_nonneg hL.1.le]
      calc
        _ ≤ (162*(1/10000:ℝ))*1 :=
          mul_le_mul (mul_le_mul hL.2 hR (abs_nonneg _) (by norm_num)) hb
            (abs_nonneg _) (by positivity)
        _ = _ := by ring
    have hshape : (∑ j : Fin p, |phiFarShape X i.val j.val - Matrix.diagonal d i j|) ≤
        2*X/3+12 := by
      rw [show (∑ j : Fin p, |phiFarShape X i.val j.val - Matrix.diagonal d i j|) =
          ∑ j ∈ Finset.range p,
            |phiFarShape X i.val j - if i.val = j then phiFarDiag X i.val else 0| by
        simp only [Matrix.diagonal_apply, d, ← Fin.val_inj]
        exact Fin.sum_univ_eq_sum_range
          (fun j : ℕ => |phiFarShape X i.val j - if i.val = j then phiFarDiag X i.val else 0|) p]
      exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hp)
        (fun k _ _ => abs_nonneg _)).trans (phiFarShape_row_bound hX ⟨i.val,hi⟩)
    have hpR : (p:ℝ) ≤ 4 := by exact_mod_cast hp
    have hS := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hs j)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hS
    linarith only [hS, hd i, hshape, hX, hpR]
  have hAdet := det_pos_of_row_diagonal_margin A d (fun i => by linarith [hd i,hX]) hrow
  have hL : 0 < ∏ i : Fin p, phiFarLeft X i.val :=
    Finset.prod_pos (fun i _ => (phiFarLeft_bounds hX (i.isLt.trans_le hp)).1)
  have hR : 0 < ∏ i : Fin p, (1:ℝ)/(3:ℝ)^i.val := Finset.prod_pos (fun _ _ => by positivity)
  have hRdet : ∏ i : Fin p, phiFarRight i.val =
      kernelMinorSign p * (∏ i : Fin p, (1:ℝ)/(3:ℝ)^i.val) := by
    simp only [phiFarRight, div_eq_mul_inv, Finset.prod_mul_distrib, one_mul, kernelMinorSign]
    rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i : ℕ => i), Finset.sum_range_id]
  apply (phiCompactMatrix_signed_det_pos_iff hp t).mp
  simp only [A, Matrix.det_mul, Matrix.det_diagonal, hRdet] at hAdet
  have he : 0 < (∏ i : Fin p, phiFarLeft X i.val) * (∏ i : Fin p, (1:ℝ)/(3:ℝ)^i.val) *
      (kernelMinorSign p * (phiCompactMatrix p X).det) := by
    convert hAdet using 1
    ring
  exact (mul_pos_iff_of_pos_left (mul_pos hL hR)).mp he

#print axioms phiFarWronskian_pos

end Nuttall
