import Nuttall.Existence
import W5.VerifiedIntervalRealSemantics
import W5.VerifiedIntervalPolynomials

open scoped BigOperators

namespace W5.QInterval

/-- The exact sum of the rational lower and upper endpoints. -/
def sumBox {α : Type*} (s : Finset α) (B : α → QInterval) : QInterval :=
  ⟨∑ i ∈ s, (B i).lo, ∑ i ∈ s, (B i).hi⟩

theorem sumBox_containsReal {α : Type*} (s : Finset α) (B : α → QInterval) (f : α → ℝ)
    (h : ∀ i ∈ s, ContainsReal (B i) (f i)) : ContainsReal (sumBox s B) (∑ i ∈ s, f i) := by
  simp only [ContainsReal, sumBox, Rat.cast_sum]
  exact ⟨Finset.sum_le_sum (fun i hi => (h i hi).1), Finset.sum_le_sum (fun i hi => (h i hi).2)⟩

/-- Laplace expansion using rational interval arithmetic. -/
def determinant : (n : ℕ) → Matrix (Fin n) (Fin n) QInterval → QInterval
  | 0, _ => ⟨1, 1⟩
  | n + 1, B =>
      let term (j : Fin (n + 1)) :=
        mul (point ((-1 : ℚ)^j.val))
          (mul (B 0 j) (determinant n (B.submatrix Fin.succ j.succAbove)))
      sumBox Finset.univ term

/-- The interval Laplace expansion encloses the determinant of any enclosed real matrix. -/
theorem determinant_containsReal (n : ℕ) (B : Matrix (Fin n) (Fin n) QInterval)
    (A : Matrix (Fin n) (Fin n) ℝ) (h : ∀ i j, ContainsReal (B i j) (A i j)) :
    ContainsReal (determinant n B) A.det := by
  induction n with
  | zero => simp [determinant, ContainsReal, Matrix.det_fin_zero]
  | succ n ih =>
    let term (j : Fin (n + 1)) :=
      mul (point ((-1 : ℚ)^j.val))
        (mul (B 0 j) (determinant n (B.submatrix Fin.succ j.succAbove)))
    have ht (j : Fin (n + 1)) : ContainsReal (term j)
        ((-1 : ℝ)^j.val * (A 0 j * (A.submatrix Fin.succ j.succAbove).det)) := by
      have hsign : ContainsReal (point ((-1 : ℚ)^j.val)) ((-1 : ℝ)^j.val) := by
        simp [ContainsReal, point, Rat.cast_pow]
      refine mul_containsReal hsign (mul_containsReal (h 0 j) (ih _ _ ?_))
      exact fun i k => h i.succ (j.succAbove k)
    rw [Matrix.det_succ_row_zero]
    simp only [determinant, mul_assoc]
    exact sumBox_containsReal Finset.univ term _ (fun j _ => ht j)

end W5.QInterval

namespace Nuttall

open W5

/-- Rational target intervals for derivatives 0 through 8 of Φ at the origin. -/
def phiOriginJetBox : ℕ → QInterval
  | 0 => ⟨44/100, 45/100⟩
  | 1 => ⟨-1/100, 1/100⟩
  | 2 => ⟨-3347/100, -3346/100⟩
  | 3 => ⟨-1, 1⟩
  | 4 => ⟨6497, 6498⟩
  | 5 => ⟨-100, 100⟩
  | 6 => ⟨-1630000, -1620000⟩
  | 7 => ⟨-1000000, 1000000⟩
  | _ => ⟨233000000, 234000000⟩

private def phiOriginHankelBox : Matrix (Fin 5) (Fin 5) QInterval :=
  Matrix.of (fun i j => phiOriginJetBox (i.val + j.val))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
theorem phiOriginHankelBox_upper :
    (QInterval.determinant 5 phiOriginHankelBox).hi ≤ -2111237149457137148 := by
  decide +kernel

/-- The certified rational matrix calculation reduces strict negativity to nine scalar
enclosures. The enclosures are explicit hypotheses of this theorem. -/
theorem phi_origin_wronskian_neg_of_jet_bounds
    (h : ∀ k ≤ 8, QInterval.ContainsReal (phiOriginJetBox k) (iteratedDeriv k Phi 0)) :
    wronskian Phi 5 0 < 0 := by
  have hd := QInterval.determinant_containsReal 5 phiOriginHankelBox
    (Matrix.of (fun i j => iteratedDeriv (i.val + j.val) Phi 0))
    (fun i j => h _ (by have := i.isLt; have := j.isLt; omega))
  exact hd.2.trans_lt (by
    exact_mod_cast phiOriginHankelBox_upper.trans_lt (by norm_num :
      (-2111237149457137148 : ℚ) < 0))

#print axioms phiOriginHankelBox_upper
#print axioms phi_origin_wronskian_neg_of_jet_bounds

end Nuttall
