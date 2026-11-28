import Nuttall.PsiCompactCell1Margin
import Nuttall.PsiCompactCell1Jets
import Nuttall.PsiCompactUniformPanel1

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor1
      (fun j => (psiOneCell1Snapshot.jets j).asQInterval (2^90)) 36
      (1/32 - psiOneDyadicCenter 1)
    (psiOneCell1Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell1Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell1_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 1/128 ≤ t) (hU : t ≤ 2/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 1 1 (by decide) (by decide +kernel)
    psiOneCompactAnchor1 ?_ psiOneCell1Snapshot psiOneCell1Inputs_checked psiOneCell1Jets_checked
    corner_checked psiOneCell1Margin_checked p hp t ?_ ?_
  · have hanchor : ((1/32:ℚ):ℝ) = (((1:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor1_containsReal
  · change (((1:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((2:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell1_signed_wronskians

end Nuttall
