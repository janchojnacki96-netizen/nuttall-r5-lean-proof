import Nuttall.PsiFirstCellCorner
import Nuttall.PsiFirstCellJetData
import Nuttall.CompactIntervalRounding

namespace Nuttall

open W5

private def firstPanelEndpoints : Array (ℤ × ℤ) := #[
  (13720172231, 13720174944),
  (12633708866, 12633711579),
  (10784638577, 10784641289),
  (8497350556, 8497353268),
  (6140969261, 6140971972),
  (4037845962, 4037848673),
  (2391849538, 2391852248),
  (1261586703, 1261589412),
  (584527874, 584530583),
  (234218381, 234221090),
  (79730145, 79732853),
  (22594286, 22596994),
  (5208526, 5211234),
  (950877, 953585),
  (132612, 135320),
  (12679, 15387)
]

private def firstPanelBounds (i : ℕ) : QInterval :=
  let ab := firstPanelEndpoints[i]!
  ⟨(ab.1:ℚ)/10^12, (ab.2:ℚ)/10^12⟩

private def zeroCornerPanel (i : ℕ) : QInterval :=
  psiOnePanelBox (QInterval.point 0) (firstCellGridJets i) 20 (1/32)

private def gridPanelCheck (i : ℕ) : Prop :=
  (firstPanelBounds i).lo ≤ (zeroCornerPanel i).lo ∧
  (zeroCornerPanel i).hi ≤ (firstPanelBounds i).hi

private instance (i : ℕ) : Decidable (gridPanelCheck i) := by
  unfold gridPanelCheck
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 40000000 in
private theorem gridPanelCheck_of_lt (i : ℕ) (hi : i < 16) : gridPanelCheck i := by
  interval_cases i <;> decide +kernel

private def snappedCornerGrid : ℕ → ℕ → QInterval
  | _, 0 => firstCellGridSeed
  | i, n+1 => QInterval.add (snappedCornerGrid (i+1) n) (firstPanelBounds i)

private theorem snappedCornerGrid_bounds (i n : ℕ) (h : i+n ≤ 16) :
    (snappedCornerGrid i n).lo ≤
        (psiOneUniformGridBox firstCellGridSeed firstCellGridJets 20 (1/32) i n).lo ∧
    (psiOneUniformGridBox firstCellGridSeed firstCellGridJets 20 (1/32) i n).hi ≤
        (snappedCornerGrid i n).hi := by
  induction n generalizing i with
  | zero => simp only [snappedCornerGrid, psiOneUniformGridBox, le_refl, and_self]
  | succ n ih =>
    have hprev := ih (i+1) (by omega)
    have hpanel := gridPanelCheck_of_lt i (by omega)
    rw [psiOneUniformGridBox, psiOnePanelBox_eq_add_zero, snappedCornerGrid]
    exact ⟨add_le_add hprev.1 hpanel.1, add_le_add hprev.2 hpanel.2⟩

private theorem psiOneFirstCellCorner_endpoints :
    psiOneFirstCellFixedCorner.lo ≤ psiOneFirstCellCornerBox.lo ∧
    psiOneFirstCellCornerBox.hi ≤ psiOneFirstCellFixedCorner.hi := by
  have hbase : psiOneFirstCellFixedCorner.lo ≤ (snappedCornerGrid 0 16).lo ∧
      (snappedCornerGrid 0 16).hi ≤ psiOneFirstCellFixedCorner.hi := by decide +kernel
  have h := snappedCornerGrid_bounds 0 16 (by decide)
  exact ⟨hbase.1.trans h.1, h.2.trans hbase.2⟩

theorem psiOneFirstCellFixedCorner_containsReal :
    psiOneFirstCellFixedCorner.ContainsReal (psi 1 (1/256)) :=
  compactContainsReal_of_endpoints psiOneFirstCellCorner_endpoints.1
    psiOneFirstCellCorner_endpoints.2 psiOne_first_cell_corner_containsReal

#print axioms psiOneFirstCellFixedCorner_containsReal

end Nuttall
