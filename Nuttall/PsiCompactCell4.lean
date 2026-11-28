import Nuttall.PsiCompactCell4Margin
import Nuttall.PsiCompactCell4Jets
import Nuttall.PsiCompactUniformPanel2

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor2
      (fun j => (psiOneCell4Snapshot.jets j).asQInterval (2^90)) 36
      (2/32 - psiOneDyadicCenter 4)
    (psiOneCell4Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell4Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell4_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 4/128 ≤ t) (hU : t ≤ 5/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 4 2 (by decide) (by decide +kernel)
    psiOneCompactAnchor2 ?_ psiOneCell4Snapshot psiOneCell4Inputs_checked psiOneCell4Jets_checked
    corner_checked psiOneCell4Margin_checked p hp t ?_ ?_
  · have hanchor : ((2/32:ℚ):ℝ) = (((2:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor2_containsReal
  · change (((4:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((5:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell4_signed_wronskians

end Nuttall
