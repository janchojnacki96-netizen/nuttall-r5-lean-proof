import Nuttall.PsiCompactCell7Margin
import Nuttall.PsiCompactCell7Jets
import Nuttall.PsiCompactUniformPanel2

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor2
      (fun j => (psiOneCell7Snapshot.jets j).asQInterval (2^90)) 36
      (2/32 - psiOneDyadicCenter 7)
    (psiOneCell7Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell7Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell7_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 7/128 ≤ t) (hU : t ≤ 8/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 7 2 (by decide) (by decide +kernel)
    psiOneCompactAnchor2 ?_ psiOneCell7Snapshot psiOneCell7Inputs_checked psiOneCell7Jets_checked
    corner_checked psiOneCell7Margin_checked p hp t ?_ ?_
  · have hanchor : ((2/32:ℚ):ℝ) = (((2:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor2_containsReal
  · change (((7:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((8:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell7_signed_wronskians

end Nuttall
