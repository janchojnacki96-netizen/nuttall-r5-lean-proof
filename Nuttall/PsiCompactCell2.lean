import Nuttall.PsiCompactCell2Margin
import Nuttall.PsiCompactCell2Jets
import Nuttall.PsiCompactUniformPanel1

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor1
      (fun j => (psiOneCell2Snapshot.jets j).asQInterval (2^90)) 36
      (1/32 - psiOneDyadicCenter 2)
    (psiOneCell2Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell2Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell2_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 2/128 ≤ t) (hU : t ≤ 3/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 2 1 (by decide) (by decide +kernel)
    psiOneCompactAnchor1 ?_ psiOneCell2Snapshot psiOneCell2Inputs_checked psiOneCell2Jets_checked
    corner_checked psiOneCell2Margin_checked p hp t ?_ ?_
  · have hanchor : ((1/32:ℚ):ℝ) = (((1:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor1_containsReal
  · change (((2:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((3:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell2_signed_wronskians

end Nuttall
