import Nuttall.CompactPolynomialMargin
import Nuttall.CompactIntervalCongruence

namespace Nuttall

open W5
open scoped BigOperators

private def compactSignDiagonal {n : ℕ} (k : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.diagonal fun i => if k = 0 then (-1 : ℚ)^i.val else 0

/-- Apply the rational basis to each coefficient and remove the sign diagonal
from the constant coefficient. -/
def compactCenteredCoefficientBoxes {n : ℕ} (U : Matrix (Fin n) (Fin n) ℚ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) QInterval) (k : ℕ) :
    Matrix (Fin n) (Fin n) QInterval :=
  Matrix.of fun i j =>
    (compactIntervalCongruence U (boxes k) i j).sub
      (QInterval.point (compactSignDiagonal k i j))

/-- Apply the real congruence to one coefficient and subtract its sign matrix. -/
noncomputable def compactCenteredRealCoefficients {n : ℕ} (U : Matrix (Fin n) (Fin n) ℚ)
    (poly : ℕ → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  let V := U.map (fun r : ℚ => (r:ℝ))
  let J := Matrix.diagonal (fun i : Fin n => (-1 : ℝ)^i.val)
  V * poly k * V.transpose - (if k = 0 then J else 0)

/-- Any sound centered coefficient enclosures and a strict row bound
certify the signed leading minors on the whole cell. -/
theorem signed_leading_det_pos_of_centeredCertificate {p n d : ℕ} (hp : p ≤ n) (hd : 0 < d)
    (A : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℚ)
    (hU : U.IsLowerTriangular) (hdiag : ∀ i, U i i ≠ 0)
    (v : ℝ) (hv : |v| ≤ 1) (ρ M : ℚ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (poly : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) QInterval)
    (hbox : ∀ k ∈ Finset.range d, ∀ i j, (boxes k i j).ContainsReal
      (compactCenteredRealCoefficients U poly k i j))
    (herr : ∀ i j, |A i j - ∑ k ∈ Finset.range d, poly k i j * v^k| ≤ (ρ:ℝ))
    (hrows : ∀ i, (∑ j, |U i j|) ≤ M)
    (hcheck : ∀ i, compactPolynomialRowBound d boxes i +
      (n:ℚ)*(ρ*M*M) < 1) :
    0 < kernelMinorSign p * (A.submatrix (Fin.castLE hp) (Fin.castLE hp)).det := by
  let V := U.map (fun r : ℚ => (r:ℝ))
  let J := Matrix.diagonal (fun i : Fin n => (-1 : ℝ)^i.val)
  let P := ∑ k ∈ Finset.range d, v^k • poly k
  let centered (k : ℕ) := V * poly k * V.transpose -
    (if k = 0 then J else 0)
  have hV : V.IsLowerTriangular := by
    intro i j h
    change (↑(U i j) : ℝ) = 0
    exact_mod_cast hU h
  have hdV : ∀ i, V i i ≠ 0 := by
    intro i
    change (↑(U i i) : ℝ) ≠ 0
    exact_mod_cast hdiag i
  have hsum : V * P * V.transpose = ∑ k ∈ Finset.range d, v^k • (V * poly k * V.transpose) := by
    simp only [P, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hpoly (i j : Fin n) : ∑ k ∈ Finset.range d, centered k i j * v^k =
      (V * P * V.transpose) i j - J i j := by
    rw [hsum]
    simp only [centered, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib, Matrix.sum_apply,
      Matrix.smul_apply, smul_eq_mul]
    congr 1
    · exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    · rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        simp [hk]
      · simp [hd]
  have hP (i j : Fin n) : P i j = ∑ k ∈ Finset.range d, poly k i j * v^k := by
    simp only [P, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  have hE (i j : Fin n) : |(A-P) i j| ≤ (ρ:ℝ) := by
    rw [Matrix.sub_apply, hP]
    exact herr i j
  have hR (i : Fin n) : ∑ j, |V i j| ≤ (M:ℝ) := by
    change (∑ j, |(↑(U i j):ℝ)|) ≤ (M:ℝ)
    exact_mod_cast hrows i
  apply signed_leading_det_pos_of_compactPolynomial hp A V hV hdV d v hv (ρ*M*M)
    centered boxes hbox _ hcheck
  intro i j
  change |(V*A*V.transpose) i j - J i j - _| ≤ _
  rw [hpoly]
  have he : (V*A*V.transpose) i j - J i j - ((V*P*V.transpose) i j-J i j) =
      (V*(A-P)*V.transpose) i j := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_apply]
    ring
  rw [he, Rat.cast_mul, Rat.cast_mul]
  have hρR : 0 ≤ (ρ:ℝ) := by exact_mod_cast hρ
  have hMR : 0 ≤ (M:ℝ) := by exact_mod_cast hM
  refine (congruence_entry_abs_le V (A-P) hE i j).trans ?_
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hR i) hρR) (hR j)
    (Finset.sum_nonneg fun k _ => abs_nonneg (V j k)) (mul_nonneg hρR hMR)

theorem compactCenteredCoefficientBoxes_containsReal {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℚ)
    {boxes : ℕ → Matrix (Fin n) (Fin n) QInterval}
    {poly : ℕ → Matrix (Fin n) (Fin n) ℝ} {k : ℕ}
    (hbox : ∀ i j, (boxes k i j).ContainsReal (poly k i j)) (i j : Fin n) :
    (compactCenteredCoefficientBoxes U boxes k i j).ContainsReal
      (compactCenteredRealCoefficients U poly k i j) := by
  let V := U.map (fun r : ℚ => (r:ℝ))
  let J := Matrix.diagonal (fun i : Fin n => (-1 : ℝ)^i.val)
  have hsign : (↑(compactSignDiagonal (n := n) k i j) : ℝ) =
      (if k = 0 then J else 0) i j := by
    by_cases hk₀ : k = 0 <;> by_cases hij : i = j <;>
      simp [compactSignDiagonal, J, hk₀, hij]
  change (compactCenteredCoefficientBoxes U boxes k i j).ContainsReal
    ((V * poly k * V.transpose - (if k = 0 then J else 0)) i j)
  apply QInterval.sub_containsReal (compactIntervalCongruence_containsReal U (hbox) i j)
  exact ⟨hsign.le, hsign.ge⟩

/-- A single margin check on the original interval coefficients and their
entrywise remainder controls the signed leading minors on the whole cell. -/
theorem signed_leading_det_pos_of_compactCertificate {p n d : ℕ} (hp : p ≤ n) (hd : 0 < d)
    (A : Matrix (Fin n) (Fin n) ℝ) (U : Matrix (Fin n) (Fin n) ℚ)
    (hU : U.IsLowerTriangular) (hdiag : ∀ i, U i i ≠ 0)
    (v : ℝ) (hv : |v| ≤ 1) (ρ M : ℚ) (hρ : 0 ≤ ρ) (hM : 0 ≤ M)
    (poly : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) QInterval)
    (hbox : ∀ k ∈ Finset.range d, ∀ i j, (boxes k i j).ContainsReal (poly k i j))
    (herr : ∀ i j, |A i j - ∑ k ∈ Finset.range d, poly k i j * v^k| ≤ (ρ:ℝ))
    (hrows : ∀ i, (∑ j, |U i j|) ≤ M)
    (hcheck : ∀ i, compactPolynomialRowBound d (compactCenteredCoefficientBoxes U boxes) i +
      (n:ℚ)*(ρ*M*M) < 1) :
    0 < kernelMinorSign p * (A.submatrix (Fin.castLE hp) (Fin.castLE hp)).det := by
  exact signed_leading_det_pos_of_centeredCertificate hp hd A U hU hdiag v hv ρ M hρ hM
    poly (compactCenteredCoefficientBoxes U boxes) (fun k hk => compactCenteredCoefficientBoxes_containsReal U (hbox k hk)) herr hrows hcheck

#print axioms signed_leading_det_pos_of_centeredCertificate
#print axioms signed_leading_det_pos_of_compactCertificate

end Nuttall
