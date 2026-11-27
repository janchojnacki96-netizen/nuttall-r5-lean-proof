import Nuttall.CompactFixedCongruence
import Nuttall.PsiCompactBasisData
import Nuttall.PsiCompactCellSigns

namespace Nuttall

open W5

private def matrixScale : ℤ := 2^90

private theorem matrixScale_pos : 0 < matrixScale := by
  unfold matrixScale
  positivity

private def fixedBasis (i : Fin 67) : Matrix (Fin 7) (Fin 7) ℤ :=
  (psiOneCompactBasisNumerator i).map (fun u => u*2^80)

private theorem fixedBasis_real (i : Fin 67) :
    (fixedBasis i).map (fun u => (u:ℝ)/matrixScale) =
    (psiOneCompactBasis i).map (fun u : ℚ => (u:ℝ)) := by
  ext a b
  simp only [fixedBasis, psiOneCompactBasis, Matrix.map_apply, Rat.cast_div, Rat.cast_ofNat,
    Rat.cast_intCast, Int.cast_mul, Int.cast_pow, Int.cast_ofNat, matrixScale]
  ring

private def fixedCenteredBoxes (i : Fin 67) (boxes : ℕ → Matrix (Fin 7) (Fin 7) QInterval)
    (k : ℕ) : Matrix (Fin 7) (Fin 7) FixedIntInterval :=
  compactFixedCenteredCoefficient matrixScale (fixedBasis i)
    (fun l => (boxes l).map (compactFixedRound matrixScale)) k

/-- Integer row numerators for the finite rank-seven certificate. -/
def psiOneCompactFixedRow (i : Fin 67) (boxes : ℕ → Matrix (Fin 7) (Fin 7) QInterval)
    (j : Fin 7) : ℤ :=
  compactFixedRowNumerator 25 (fixedCenteredBoxes i boxes) j

def psiOneCompactFixedThreshold : ℤ := 7*matrixScale/10

theorem psiOne_compact_fixed_cell_signed_wronskians {p : ℕ} (hp : p ≤ 7)
    {c h v : ℝ} (ha : 0 ≤ c-h) (hb : c+h ≤ 2) (hh : 0 ≤ h) (hh' : h ≤ 1/256)
    (hv : |v| ≤ 1) (i : Fin 67) (boxes : ℕ → Matrix (Fin 7) (Fin 7) QInterval)
    (hbox : ∀ k < 25, ∀ a b, (boxes k a b).ContainsReal
      (psiOneCompactRealCoefficients c h k a b))
    (hcheck : ∀ j, psiOneCompactFixedRow i boxes j < psiOneCompactFixedThreshold) :
    0 < kernelMinorSign p * wronskian (psi 1) p (c+h*v) := by
  let centered (k : ℕ) := (fixedCenteredBoxes i boxes k).map (FixedIntInterval.asQInterval matrixScale)
  apply psiOne_compact_centered_cell_signed_wronskians hp ha hb hh hh' hv (psiOneCompactBasis i)
    (psiOneCompactBasis_lower i) (psiOneCompactBasis_diagonal_ne_zero i) 20000000
    (by norm_num) (psiOneCompactBasis_row_le i) centered
  · intro k hk a b
    have hproof := compactFixedCenteredCoefficient_containsReal matrixScale matrixScale_pos
      (fixedBasis i) (boxes := fun l => (boxes l).map (compactFixedRound matrixScale))
      (poly := psiOneCompactRealCoefficients c h) k
      (fun x y => compactFixedRound_containsReal matrixScale_pos (hbox k hk x y)) a b
    simpa only [centered, Matrix.map_apply, fixedCenteredBoxes, compactCenteredRealCoefficients,
      fixedBasis_real] using hproof
  · intro j
    exact compactFixedRow_lt_one matrixScale matrixScale_pos 25 (fixedCenteredBoxes i boxes)
      j ((1/10^19)*20000000*20000000) psiOneCompactFixedThreshold (hcheck j) (by decide +kernel)

#print axioms psiOne_compact_fixed_cell_signed_wronskians

end Nuttall
