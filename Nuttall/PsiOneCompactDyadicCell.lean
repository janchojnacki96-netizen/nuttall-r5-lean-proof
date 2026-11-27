import Nuttall.CompactDyadicCoefficients
import Nuttall.PsiCompactBasisData
import Nuttall.PsiCompactCellSigns

namespace Nuttall

open W5

private def matrixScale : ℤ := 2^90

private theorem matrixScale_pos : 0 < matrixScale := by
  unfold matrixScale
  positivity

private def jetFromPhi (corner : FixedIntInterval) (phi : ℕ → FixedIntInterval) :
    ℕ → FixedIntInterval
  | 0 => corner
  | k+1 => ⟨-(phi k).hi, -(phi k).lo⟩

private def rawCoefficients (corner : FixedIntInterval) (phi : ℕ → FixedIntInterval) (k : ℕ) :
    Matrix (Fin 7) (Fin 7) FixedIntInterval :=
  Matrix.of fun i j =>
    compactDyadicCoefficient 8 (i.val+j.val) k (jetFromPhi corner phi (i.val+j.val+k))

private def fixedBasis (i : Fin 67) : Matrix (Fin 7) (Fin 7) ℤ :=
  (psiOneCompactBasisNumerator i).map (· * 2^80)

private def centered (i : Fin 67) (corner : FixedIntInterval) (phi : ℕ → FixedIntInterval)
    (k : ℕ) : Matrix (Fin 7) (Fin 7) FixedIntInterval :=
  compactFixedCenteredCoefficient matrixScale (fixedBasis i) (rawCoefficients corner phi) k

/-- Integer-only row check for the uniform prefix of the rank-seven grid. -/
def psiOneCompactDyadicRow (i : Fin 67) (corner : FixedIntInterval)
    (phi : ℕ → FixedIntInterval) (j : Fin 7) : ℤ :=
  compactFixedRowNumerator 25 (centered i corner phi) j

def psiOneCompactDyadicThreshold : ℤ := 7*matrixScale/10

/-- Replay a rank-seven compact cell of radius 1/256 without rational arithmetic in its row check. -/
theorem psiOne_compact_dyadic_cell_signed_wronskians {p : ℕ} (hp : p ≤ 7)
    {c v : ℝ} (ha : 0 ≤ c-1/256) (hb : c+1/256 ≤ 2) (hv : |v| ≤ 1) (i : Fin 67)
    {corner : FixedIntInterval} {phi : ℕ → FixedIntInterval}
    (hcorner : (corner.asQInterval matrixScale).ContainsReal (psi 1 c))
    (hphi : ∀ j < 36, ((phi j).asQInterval matrixScale).ContainsReal (iteratedDeriv j Phi c))
    (hcheck : ∀ j, psiOneCompactDyadicRow i corner phi j < psiOneCompactDyadicThreshold) :
    0 < kernelMinorSign p * wronskian (psi 1) p (c+(1/256)*v) := by
  let boxes (k : ℕ) := (centered i corner phi k).map (FixedIntInterval.asQInterval matrixScale)
  have hjet (n : ℕ) (hn : n ≤ 36) : ((jetFromPhi corner phi n).asQInterval matrixScale).ContainsReal
      (iteratedDeriv n (psi 1) c) := by
    cases n with
    | zero => simpa only [jetFromPhi, iteratedDeriv_zero] using hcorner
    | succ n =>
      rw [show (1:ℕ) = 0+1 by rfl, iteratedDeriv_succ_psi_succ]
      simpa only [psi, jetFromPhi, FixedIntInterval.asQInterval, QInterval.neg, Int.cast_neg, neg_div]
        using QInterval.neg_containsReal (hphi n (by omega))
  have hmap : ((fixedBasis i).map (fun x : ℤ => (x:ℝ)/matrixScale)) =
      (psiOneCompactBasis i).map (fun x : ℚ => (x:ℝ)) := by
    ext a b
    simp only [psiOneCompactBasis, fixedBasis, Matrix.map_apply, matrixScale,
      Rat.cast_div, Rat.cast_ofNat, Rat.cast_intCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
    ring
  apply psiOne_compact_centered_cell_signed_wronskians hp ha hb (by norm_num) le_rfl hv
    (psiOneCompactBasis i) (psiOneCompactBasis_lower i) (psiOneCompactBasis_diagonal_ne_zero i)
    20000000 (by norm_num) (psiOneCompactBasis_row_le i) boxes
  · intro k hk a b
    have hraw (a b : Fin 7) :
        ((rawCoefficients corner phi k a b).asQInterval matrixScale).ContainsReal
          (psiOneCompactRealCoefficients c (1/256) k a b) := by
      have ha := a.isLt
      have hb := b.isLt
      have h := compactDyadicCoefficient_containsReal matrixScale_pos
        (hjet (a.val+b.val+k) (by omega)) 8 (a.val+b.val) k
      simpa only [rawCoefficients, psiOneCompactRealCoefficients, Matrix.of_apply,
        show (2:ℝ)^8 = 256 by norm_num] using h
    have h := compactFixedCenteredCoefficient_containsReal matrixScale matrixScale_pos
      (fixedBasis i) k hraw a b
    simpa only [boxes, Matrix.map_apply, centered, compactCenteredRealCoefficients, hmap] using h
  · intro j
    exact compactFixedRow_lt_one matrixScale matrixScale_pos 25 (centered i corner phi)
      j ((1/10^19)*20000000*20000000) psiOneCompactDyadicThreshold (hcheck j) (by decide +kernel)

#print axioms psiOne_compact_dyadic_cell_signed_wronskians

end Nuttall
