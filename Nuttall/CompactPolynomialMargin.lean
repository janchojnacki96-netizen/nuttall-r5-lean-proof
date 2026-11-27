import Nuttall.MatrixCongruenceMargin
import W5.VerifiedIntervalRealSemantics

namespace Nuttall

open W5
open scoped BigOperators

private def intervalMagnitude (I : QInterval) : ℚ := max |I.lo| |I.hi|

private theorem abs_le_intervalMagnitude {I : QInterval} {x : ℝ} (h : I.ContainsReal x) :
    |x| ≤ (intervalMagnitude I : ℝ) := by
  unfold intervalMagnitude
  rw [Rat.cast_mono.map_max, Rat.cast_abs, Rat.cast_abs]
  exact abs_le.mpr ⟨(neg_le_neg ((neg_le_abs _).trans (le_max_left _ _))).trans_eq
    (neg_neg _) |>.trans h.1, h.2.trans ((le_abs_self _).trans (le_max_right _ _))⟩

/-- Propagate a uniform entry error through a congruence using the absolute
row sums of the two selected rows. -/
theorem congruence_entry_abs_le {n : ℕ} (U E : Matrix (Fin n) (Fin n) ℝ) {ρ : ℝ}
    (hE : ∀ i j, |E i j| ≤ ρ) (i j : Fin n) :
    |(U * E * U.transpose) i j| ≤
      (ρ * (∑ a : Fin n, |U i a|)) * (∑ b : Fin n, |U j b|) := by
  have hinner (b : Fin n) : |(U * E) i b| ≤ ρ * ∑ a : Fin n, |U i a| := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
    intro a _
    rw [abs_mul, mul_comm ρ]
    exact mul_le_mul_of_nonneg_left (hE a b) (abs_nonneg _)
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro b _
  rw [abs_mul, Matrix.transpose_apply]
  exact mul_le_mul_of_nonneg_right (hinner b) (abs_nonneg _)

/-- A rational row bound for a polynomial whose coefficients are interval matrices. -/
def compactPolynomialRowBound {n : ℕ} (d : ℕ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) QInterval) (i : Fin n) : ℚ :=
  ∑ k ∈ Finset.range d, ∑ j : Fin n, intervalMagnitude (boxes k i j)

/-- Verified coefficient and remainder bounds imply all the signed leading
minors at once. The coefficient boxes enclose the transformed polynomial
with the sign diagonal removed from its constant term. -/
theorem signed_leading_det_pos_of_compactPolynomial {p n : ℕ} (hp : p ≤ n)
    (A U : Matrix (Fin n) (Fin n) ℝ) (hU : U.IsLowerTriangular) (hdiag : ∀ i, U i i ≠ 0)
    (d : ℕ) (v : ℝ) (hv : |v| ≤ 1) (δ : ℚ)
    (poly : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (boxes : ℕ → Matrix (Fin n) (Fin n) QInterval)
    (hbox : ∀ k ∈ Finset.range d, ∀ i j, (boxes k i j).ContainsReal (poly k i j))
    (herr : ∀ i j, |(U * A * U.transpose) i j -
      Matrix.diagonal (fun l : Fin n => (-1:ℝ)^l.val) i j -
        ∑ k ∈ Finset.range d, poly k i j * v^k| ≤ (δ:ℝ))
    (hcheck : ∀ i, compactPolynomialRowBound d boxes i + (n:ℚ)*δ < 1) :
    0 < kernelMinorSign p * (A.submatrix (Fin.castLE hp) (Fin.castLE hp)).det := by
  apply signed_leading_det_pos_of_triangular_congruence hp A U hU hdiag
  intro i
  let b (j : Fin n) := (U * A * U.transpose) i j -
    Matrix.diagonal (fun l : Fin n => (-1:ℝ)^l.val) i j
  let M (k : ℕ) (j : Fin n) := (intervalMagnitude (boxes k i j) : ℝ)
  have hmono (j : Fin n) : |b j| ≤ (δ:ℝ) + ∑ k ∈ Finset.range d, M k j := by
    let vSum := ∑ k ∈ Finset.range d, poly k i j * v^k
    have hpoly : |vSum| ≤ ∑ k ∈ Finset.range d, M k j := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
      intro k hk
      rw [abs_mul, abs_pow]
      exact (mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hv)).trans
        (abs_le_intervalMagnitude (hbox k hk i j))
    calc
      |b j| = |(b j - vSum) + vSum| := by rw [sub_add_cancel]
      _ ≤ |b j - vSum| + |vSum| := abs_add_le _ _
      _ ≤ _ := add_le_add (herr i j) hpoly
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => hmono j)
  have hcast : (compactPolynomialRowBound d boxes i : ℝ) + (n:ℝ)*(δ:ℝ) < 1 := by
    exact_mod_cast hcheck i
  refine hsum.trans_lt ?_
  rw [Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simpa only [compactPolynomialRowBound, Rat.cast_sum, M, add_comm] using hcast

#print axioms signed_leading_det_pos_of_compactPolynomial

end Nuttall
