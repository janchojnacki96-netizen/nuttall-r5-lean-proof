import Nuttall.CompactPolynomialCertificate
import Nuttall.PsiCompactCellExpansion

namespace Nuttall

open W5
open scoped BigOperators

private noncomputable def scaledHankel (t : ℝ) : Matrix (Fin 7) (Fin 7) ℝ :=
  Matrix.of fun i j => (1/16:ℝ)^(i.val+j.val) * iteratedDeriv (i.val+j.val) (psi 1) t

private theorem scaledLeading_det {p : ℕ} (hp : p ≤ 7) (t : ℝ) :
    ((scaledHankel t).submatrix (Fin.castLE hp) (Fin.castLE hp)).det =
      ((Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)).det)^2 *
        wronskian (psi 1) p t := by
  let D := Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)
  let H : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun i j => iteratedDeriv (i.val+j.val) (psi 1) t
  have he : (scaledHankel t).submatrix (Fin.castLE hp) (Fin.castLE hp) = D*H*D := by
    ext i j
    simp only [scaledHankel, Matrix.submatrix_apply, Matrix.of_apply,
      Fin.val_castLE, D, H, Matrix.mul_diagonal, Matrix.diagonal_mul, pow_add]
    ring
  rw [he, Matrix.det_mul, Matrix.det_mul]
  change D.det * H.det * D.det = D.det^2 * H.det
  ring

/-- The scaled Taylor coefficients used by the compact rank-seven checker. -/
noncomputable def psiOneCompactRealCoefficients (c h : ℝ) (k : ℕ) :
    Matrix (Fin 7) (Fin 7) ℝ := Matrix.of fun i j =>
  (1/16:ℝ)^(i.val+j.val) * h^k/(k.factorial:ℝ) *
    iteratedDeriv (i.val+j.val+k) (psi 1) c

/-- Transfer a centered interval certificate through the Hankel scaling. -/
theorem psiOne_compact_centered_cell_signed_wronskians {p : ℕ} (hp : p ≤ 7)
    {c h v : ℝ} (ha : 0 ≤ c-h) (hb : c+h ≤ 2) (hh : 0 ≤ h) (hh' : h ≤ 1/256)
    (hv : |v| ≤ 1) (U : Matrix (Fin 7) (Fin 7) ℚ) (hU : U.IsLowerTriangular)
    (hdiag : ∀ i, U i i ≠ 0) (M : ℚ) (hM : 0 ≤ M)
    (hrows : ∀ i, (∑ j, |U i j|) ≤ M)
    (boxes : ℕ → Matrix (Fin 7) (Fin 7) QInterval)
    (hbox : ∀ k < 25, ∀ i j, (boxes k i j).ContainsReal
      (compactCenteredRealCoefficients U (psiOneCompactRealCoefficients c h) k i j))
    (hcheck : ∀ i, compactPolynomialRowBound 25 boxes i + 7*((1/10^19)*M*M) < 1) :
    0 < kernelMinorSign p * wronskian (psi 1) p (c+h*v) := by
  let C := psiOneCompactRealCoefficients c h
  have hrem (i j : Fin 7) : |scaledHankel (c+h*v) i j -
      ∑ k ∈ Finset.range 25, C k i j * v^k| ≤ ((1/10^19:ℚ):ℝ) := by
    simpa only [scaledHankel, C, psiOneCompactRealCoefficients, Matrix.of_apply, Rat.cast_div, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat] using
      psiOne_compact_scaled_entry_error_le (i.val+j.val) (by omega) ha hb hh hh' hv
  have hdet :=
    signed_leading_det_pos_of_centeredCertificate hp (d := 25) (by decide)
      (scaledHankel (c+h*v)) U hU hdiag v hv (1/10^19) M (by norm_num) hM C boxes
      (fun k hk i j => hbox k (Finset.mem_range.mp hk) i j) hrem hrows hcheck
  rw [scaledLeading_det hp] at hdet
  have hD : 0 < (Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)).det := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos (fun _ _ => by positivity)
  exact (mul_pos_iff_of_pos_left (pow_pos hD 2)).mp (by
    convert hdet using 1
    ring)

/-- Apply the same rank-seven finite check throughout any compact cell
of half-width at most 1/256. -/
theorem psiOne_compact_cell_signed_wronskians {p : ℕ} (hp : p ≤ 7)
    {c h v : ℝ} (ha : 0 ≤ c-h) (hb : c+h ≤ 2) (hh : 0 ≤ h) (hh' : h ≤ 1/256)
    (hv : |v| ≤ 1) (U : Matrix (Fin 7) (Fin 7) ℚ) (hU : U.IsLowerTriangular)
    (hdiag : ∀ i, U i i ≠ 0) (M : ℚ) (hM : 0 ≤ M)
    (hrows : ∀ i, (∑ j, |U i j|) ≤ M)
    (boxes : ℕ → Matrix (Fin 7) (Fin 7) QInterval)
    (hbox : ∀ k < 25, ∀ i j, (boxes k i j).ContainsReal
      ((1/16:ℝ)^(i.val+j.val) * h^k/(k.factorial:ℝ) *
        iteratedDeriv (i.val+j.val+k) (psi 1) c))
    (hcheck : ∀ i, compactPolynomialRowBound 25 (compactCenteredCoefficientBoxes U boxes) i +
      7*((1/10^19)*M*M) < 1) :
    0 < kernelMinorSign p * wronskian (psi 1) p (c+h*v) := by
  apply psiOne_compact_centered_cell_signed_wronskians hp ha hb hh hh' hv U hU hdiag M hM
    hrows (compactCenteredCoefficientBoxes U boxes) _ hcheck
  intro k hk i j
  exact compactCenteredCoefficientBoxes_containsReal U (hbox k hk) i j

#print axioms psiOne_compact_cell_signed_wronskians

end Nuttall
