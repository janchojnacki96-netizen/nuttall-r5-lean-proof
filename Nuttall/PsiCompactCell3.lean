import Nuttall.PsiCompactCell3Margin
import Nuttall.PsiCompactCell3Jets
import Nuttall.PsiCompactUniformPanel1

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor1
      (fun j => (psiOneCell3Snapshot.jets j).asQInterval (2^90)) 36
      (1/32 - psiOneDyadicCenter 3)
    (psiOneCell3Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell3Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell3_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 3/128 ≤ t) (hU : t ≤ 4/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 3 1 (by decide) (by decide +kernel)
    psiOneCompactAnchor1 ?_ psiOneCell3Snapshot psiOneCell3Inputs_checked psiOneCell3Jets_checked
    corner_checked psiOneCell3Margin_checked p hp t ?_ ?_
  · have hanchor : ((1/32:ℚ):ℝ) = (((1:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor1_containsReal
  · change (((3:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((4:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell3_signed_wronskians

end Nuttall
