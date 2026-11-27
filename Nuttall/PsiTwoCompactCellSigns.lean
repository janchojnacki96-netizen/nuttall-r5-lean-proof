import Nuttall.CompactDyadicCoefficients
import Nuttall.CompactPolynomialCertificate
import Nuttall.PsiTwoPanelIdentity

namespace Nuttall

open W5
open scoped BigOperators

private def matrixScale : ℤ := 2^90

private theorem matrixScale_pos : 0 < matrixScale := by
  unfold matrixScale
  positivity

private noncomputable def scaledHankel (t : ℝ) : Matrix (Fin 8) (Fin 8) ℝ :=
  Matrix.of fun i j => (1/16:ℝ)^(i.val+j.val) * iteratedDeriv (i.val+j.val) (psi 2) t

private theorem scaledLeading_det {p : ℕ} (hp : p ≤ 8) (t : ℝ) :
    ((scaledHankel t).submatrix (Fin.castLE hp) (Fin.castLE hp)).det =
      ((Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)).det)^2 *
        wronskian (psi 2) p t := by
  let D := Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)
  let H : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of fun i j => iteratedDeriv (i.val+j.val) (psi 2) t
  have he : (scaledHankel t).submatrix (Fin.castLE hp) (Fin.castLE hp) = D*H*D := by
    ext i j
    simp only [scaledHankel, Matrix.submatrix_apply, Matrix.of_apply,
      Fin.val_castLE, D, H, Matrix.mul_diagonal, Matrix.diagonal_mul, pow_add]
    ring
  rw [he, Matrix.det_mul, Matrix.det_mul]
  change D.det * H.det * D.det = D.det^2 * H.det
  ring

private noncomputable def coefficients (c : ℝ) (k : ℕ) :
    Matrix (Fin 8) (Fin 8) ℝ := Matrix.of fun i j =>
  (1/16:ℝ)^(i.val+j.val) * (1/256:ℝ)^k / (k.factorial:ℝ) *
    iteratedDeriv (i.val+j.val+k) (psi 2) c

private def jetFromPhi (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval) :
    ℕ → FixedIntInterval
  | 0 => two
  | 1 => ⟨-one.hi, -one.lo⟩
  | m+2 => phi m

private theorem jetFromPhi_containsReal {c : ℝ} {one two : FixedIntInterval}
    {phi : ℕ → FixedIntInterval}
    (h₁ : (one.asQInterval matrixScale).ContainsReal (psi 1 c))
    (h₂ : (two.asQInterval matrixScale).ContainsReal (psi 2 c))
    (hphi : ∀ j < 36, ((phi j).asQInterval matrixScale).ContainsReal (iteratedDeriv j Phi c))
    (n : ℕ) (hn : n < 38) :
    ((jetFromPhi one two phi n).asQInterval matrixScale).ContainsReal (iteratedDeriv n (psi 2) c) := by
  match n with
  | 0 => simpa only [jetFromPhi, iteratedDeriv_zero] using h₂
  | 1 =>
    rw [show (1:ℕ) = 0+1 by rfl, show (2:ℕ) = 1+1 by rfl,
      iteratedDeriv_succ_psi_succ, iteratedDeriv_zero]
    simpa only [jetFromPhi, FixedIntInterval.asQInterval, QInterval.neg, Int.cast_neg, neg_div]
      using QInterval.neg_containsReal h₁
  | n+2 =>
    rw [show n+2 = (n+1)+1 by omega, show (2:ℕ) = (0+1)+1 by rfl,
      iteratedDeriv_succ_psi_succ, iteratedDeriv_succ_psi_succ, neg_neg]
    exact hphi n (by omega)

private def rawCoefficients (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval)
    (k : ℕ) : Matrix (Fin 8) (Fin 8) FixedIntInterval :=
  Matrix.of fun i j =>
    compactDyadicCoefficient 8 (i.val+j.val) k (jetFromPhi one two phi (i.val+j.val+k))

private def centered (B : Matrix (Fin 8) (Fin 8) ℤ)
    (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval) (k : ℕ) :
    Matrix (Fin 8) (Fin 8) FixedIntInterval :=
  compactFixedCenteredCoefficient matrixScale (B.map (· * 2^80))
    (rawCoefficients one two phi) k

/-- Row sums for the rank-eight fixed-point certificate through degree 23. -/
def psiTwoCompactRow (B : Matrix (Fin 8) (Fin 8) ℤ)
    (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval) (i : Fin 8) : ℤ :=
  compactFixedRowNumerator 24 (centered B one two phi) i

def psiTwoCompactThreshold : ℤ := 3*matrixScale/5

/-- Replay a compact rank-eight certificate with an integer triangular basis. -/
theorem psiTwo_compact_fixed_cell_signed_wronskians {p : ℕ} (hp : p ≤ 8)
    {c v : ℝ} (ha : 0 ≤ c-1/256) (hb : c+1/256 ≤ 2) (hv : |v| ≤ 1)
    (B : Matrix (Fin 8) (Fin 8) ℤ) (hlower : B.IsLowerTriangular)
    (hdiag : ∀ i, B i i ≠ 0) (hrow : ∀ i, (∑ j, |B i j|) ≤ 1024*6700000)
    (one two : FixedIntInterval) (phi : ℕ → FixedIntInterval)
    (h₁ : (one.asQInterval matrixScale).ContainsReal (psi 1 c))
    (h₂ : (two.asQInterval matrixScale).ContainsReal (psi 2 c))
    (hphi : ∀ j < 36, ((phi j).asQInterval matrixScale).ContainsReal (iteratedDeriv j Phi c))
    (hcheck : ∀ i, psiTwoCompactRow B one two phi i < psiTwoCompactThreshold) :
    0 < kernelMinorSign p * wronskian (psi 2) p (c+(1/256)*v) := by
  let U := B.map (fun x : ℤ => (x:ℚ)/1024)
  have hU : U.IsLowerTriangular := by
    intro i j hij
    simp [U, hlower hij]
  have hD (i : Fin 8) : U i i ≠ 0 := by
    simpa [U] using hdiag i
  have hrows (i : Fin 8) : (∑ j, |U i j|) ≤ 6700000 := by
    simp only [U, Matrix.map_apply, abs_div, abs_of_nonneg (by norm_num : (0:ℚ) ≤ 1024),
      ← Finset.sum_div]
    rw [div_le_iff₀ (by norm_num : (0:ℚ) < 1024)]
    exact_mod_cast (show (∑ j, |B i j|) ≤ 6700000*1024 by
      simpa only [mul_comm (6700000:ℤ)] using hrow i)
  let boxes (k : ℕ) := (centered B one two phi k).map (FixedIntInterval.asQInterval matrixScale)
  have hfixed (k : ℕ) (hk : k < 24) (i j : Fin 8) :
      ((rawCoefficients one two phi k i j).asQInterval matrixScale).ContainsReal
        (coefficients c k i j) := by
    have hi := i.isLt
    have hj := j.isLt
    have h := compactDyadicCoefficient_containsReal matrixScale_pos
      (jetFromPhi_containsReal h₁ h₂ hphi (i.val+j.val+k) (by omega)) 8 (i.val+j.val) k
    simpa only [rawCoefficients, coefficients, Matrix.of_apply,
      show (2:ℝ)^8 = 256 by norm_num] using h
  have hbox (k : ℕ) (hk : k ∈ Finset.range 24) (i j : Fin 8) :
      (boxes k i j).ContainsReal (compactCenteredRealCoefficients U (coefficients c) k i j) := by
    have hmap : ((B.map (· * 2^80)).map (fun x : ℤ => (x:ℝ)/matrixScale)) =
        U.map (fun x : ℚ => (x:ℝ)) := by
      ext i j
      simp only [U, Matrix.map_apply, matrixScale, Rat.cast_div, Rat.cast_ofNat,
        Rat.cast_intCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      ring
    have h := compactFixedCenteredCoefficient_containsReal matrixScale matrixScale_pos
      (B.map (· * 2^80)) k (hfixed k (Finset.mem_range.mp hk)) i j
    simpa only [boxes, Matrix.map_apply, centered, compactCenteredRealCoefficients, hmap] using h
  have hrem (i j : Fin 8) : |scaledHankel (c+(1/256)*v) i j -
      ∑ k ∈ Finset.range 24, coefficients c k i j * v^k| ≤ ((1/10^18:ℚ):ℝ) := by
    have hi := i.isLt
    have hj := j.isLt
    have hTaylor : (1/16:ℝ)^(i.val+j.val) *
        cellTaylor (iteratedDeriv (i.val+j.val) (psi 2)) 23 c (1/256) v =
        ∑ k ∈ Finset.range 24, coefficients c k i j * v^k := by
      rw [cellTaylor, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [iteratedDeriv_iteratedDeriv_eq, Nat.add_comm k (i.val+j.val)]
      simp only [coefficients, Matrix.of_apply]
      ring
    rw [← hTaylor]
    simp only [scaledHankel, Matrix.of_apply, ← mul_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_one, Rat.cast_ofNat]
    exact psi_two_compact_scaled_error_le (i.val+j.val) (by omega)
      ha hb (by norm_num) le_rfl hv
  have hmargin (i : Fin 8) : compactPolynomialRowBound 24 boxes i +
      8*((1/10^18)*6700000*6700000) < 1 :=
    compactFixedRow_lt_one matrixScale matrixScale_pos 24 (centered B one two phi)
      i ((1/10^18)*6700000*6700000) psiTwoCompactThreshold (hcheck i) (by decide +kernel)
  have hdet :=
    signed_leading_det_pos_of_centeredCertificate hp (d := 24) (by decide)
      (scaledHankel (c+(1/256)*v)) U hU hD v hv (1/10^18) 6700000
      (by norm_num) (by norm_num) (coefficients c) boxes hbox hrem hrows hmargin
  rw [scaledLeading_det hp] at hdet
  have hpos : 0 < (Matrix.diagonal (fun i : Fin p => (1/16:ℝ)^i.val)).det := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_pos (fun _ _ => by positivity)
  exact (mul_pos_iff_of_pos_left (pow_pos hpos 2)).mp (by
    convert hdet using 1
    ring)

#print axioms psiTwo_compact_fixed_cell_signed_wronskians

end Nuttall
