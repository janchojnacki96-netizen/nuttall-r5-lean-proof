import W5.MathlibGenericSchurDeterminant
import W5.VerifiedIntervalRealSemantics
import W5.VerifiedIntervalPolynomials

namespace Nuttall

open W5

/-- Entrywise enclosure for the trailing Schur matrix. -/
def leadingSchurIntervalBlock (n : ℕ)
    (B : Matrix (Fin (1+n)) (Fin (1+n)) QInterval) : Matrix (Fin n) (Fin n) QInterval :=
  Matrix.of (fun i j => QInterval.schurUpdate
    (B (Fin.natAdd 1 i) (Fin.natAdd 1 j))
    (B (Fin.natAdd 1 i) 0) (B 0 (Fin.natAdd 1 j)) (B 0 0))

/-- Each pivot excludes zero. The supplied boxes for the next block may
round outwards, which bounds the size of exact rational arithmetic. -/
inductive SchurIntervalChain :
    (n : ℕ) → Matrix (Fin n) (Fin n) QInterval → QInterval → Prop
  | empty (B : Matrix (Fin 0) (Fin 0) QInterval) :
      SchurIntervalChain 0 B (QInterval.point 1)
  | step {n : ℕ} (B : Matrix (Fin (1+n)) (Fin (1+n)) QInterval)
      (C : Matrix (Fin n) (Fin n) QInterval) (D : QInterval)
      (hsep : 0 < (B 0 0).lo ∨ (B 0 0).hi < 0)
      (hround : ∀ i j, (C i j).lo ≤ (leadingSchurIntervalBlock n B i j).lo ∧
        (leadingSchurIntervalBlock n B i j).hi ≤ (C i j).hi)
      (hchain : SchurIntervalChain n C D) :
      SchurIntervalChain (1+n) B ((B 0 0).mul D)

theorem SchurIntervalChain.det_containsReal {n : ℕ}
    {B : Matrix (Fin n) (Fin n) QInterval} {D : QInterval}
    (hchain : SchurIntervalChain n B D) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i j, (B i j).ContainsReal (A i j)) :
    D.ContainsReal A.det := by
  induction hchain with
  | empty B => simp [Matrix.det_fin_zero, QInterval.point, QInterval.ContainsReal]
  | @step n B C D hsep hround hchain ih =>
    have h00 := hA 0 0
    have hne : A 0 0 ≠ 0 := by
      rcases hsep with hpos | hneg
      · exact ne_of_gt ((Rat.cast_pos_of_pos hpos).trans_le h00.1)
      · have h' : ((B 0 0).hi:ℝ) < 0 := by exact_mod_cast hneg
        exact ne_of_lt (h00.2.trans_lt h')
    have hNext (i j : Fin n) : (C i j).ContainsReal (leadingSchurBlock n A i j) := by
      have hS : (leadingSchurIntervalBlock n B i j).ContainsReal
          (leadingSchurBlock n A i j) := by
        simpa only [leadingSchurIntervalBlock, leadingSchurBlock, Matrix.of_apply] using
          QInterval.schurUpdate_containsReal (hA (Fin.natAdd 1 i) (Fin.natAdd 1 j))
            (hA (Fin.natAdd 1 i) 0) (hA 0 (Fin.natAdd 1 j)) h00 hsep
      have hl : ((C i j).lo:ℝ) ≤ ((leadingSchurIntervalBlock n B i j).lo:ℝ) :=
        Rat.cast_mono (hround i j).1
      have hu : ((leadingSchurIntervalBlock n B i j).hi:ℝ) ≤ ((C i j).hi:ℝ) :=
        Rat.cast_mono (hround i j).2
      exact ⟨hl.trans hS.1, hS.2.trans hu⟩
    rw [det_eq_first_pivot_mul_leadingSchurBlock n A hne]
    exact QInterval.mul_containsReal h00 (ih (leadingSchurBlock n A) hNext)

#print axioms SchurIntervalChain.det_containsReal

end Nuttall
