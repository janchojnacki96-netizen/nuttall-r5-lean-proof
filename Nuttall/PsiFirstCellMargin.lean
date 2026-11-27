import Nuttall.CompactPolynomialCertificate
import Nuttall.CompactIntervalRounding
import Nuttall.PsiFirstCellJetData

namespace Nuttall

open W5
open scoped BigOperators

/-- Dyadic lower triangular basis for the first rank-seven cell. -/
def psiOneFirstCellBasis : Matrix (Fin 7) (Fin 7) ℚ :=
  (!![4167, 0, 0, 0, 0, 0, 0;
      4252, 9203, 0, 0, 0, 0, 0;
      4287, 9537, 14068, 0, 0, 0, 0;
      4267, 15198, 14568, 19486, 0, 0, 0;
      3746, 13569, 39258, 17881, 34880, 0, 0;
      -3377, -11171, -36360, -4682, -32721, 10292, 0;
      3908, 13208, 35324, 8445, 33545, -9189, 4694] : Matrix (Fin 7) (Fin 7) ℚ).map
        (fun x => x / 1024)

theorem psiOneFirstCellBasis_lower : psiOneFirstCellBasis.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  fin_cases i <;> fin_cases j <;> norm_num [psiOneFirstCellBasis, Matrix.cons_val'] at h ⊢

theorem psiOneFirstCellBasis_diag (i : Fin 7) : psiOneFirstCellBasis i i ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem psiOneFirstCellBasis_rows (i : Fin 7) : (∑ j, |psiOneFirstCellBasis i j|) ≤ 107 := by
  fin_cases i <;> decide +kernel

/-- Interval coefficient with the center jets already snapped outwards. -/
def psiOneFirstCellReplayCoeffBox (l k : ℕ) : QInterval :=
  let J := match l+k with
    | 0 => psiOneFirstCellFixedCorner
    | j+1 => psiOneFirstCellDyadicJetBox j
  compactRoundInterval (2^90) <|
    QInterval.mul (QInterval.point ((1/16:ℚ)^l * (1/256:ℚ)^k / (k.factorial:ℚ))) J

def psiOneFirstCellReplayBoxes (k : ℕ) : Matrix (Fin 7) (Fin 7) QInterval :=
  Matrix.of fun i j => psiOneFirstCellReplayCoeffBox (i.val+j.val) k

private def psiOneFirstCellRowCheck (i : Fin 7) : Prop :=
  compactPolynomialRowBound 25 (compactCenteredCoefficientBoxes psiOneFirstCellBasis
    psiOneFirstCellReplayBoxes) i + 7 * ((1/10^19) * 107 * 107) < 13/25

private instance (i : Fin 7) : Decidable (psiOneFirstCellRowCheck i) := by
  unfold psiOneFirstCellRowCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 40000000 in
theorem psiOne_first_cell_margin_checked (i : Fin 7) :
    compactPolynomialRowBound 25 (compactCenteredCoefficientBoxes psiOneFirstCellBasis
      psiOneFirstCellReplayBoxes) i + 7 * ((1/10^19) * 107 * 107) < 13/25 := by
  change psiOneFirstCellRowCheck i
  fin_cases i <;> decide +kernel

#print axioms psiOne_first_cell_margin_checked

end Nuttall
