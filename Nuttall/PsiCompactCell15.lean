import Nuttall.PsiCompactCell15Margin
import Nuttall.PsiCompactCell15Jets
import Nuttall.PsiCompactUniformPanel4

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor4
      (fun j => (psiOneCell15Snapshot.jets j).asQInterval (2^90)) 36
      (4/32 - psiOneDyadicCenter 15)
    (psiOneCell15Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell15Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell15_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 15/128 ≤ t) (hU : t ≤ 16/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 15 4 (by decide) (by decide +kernel)
    psiOneCompactAnchor4 ?_ psiOneCell15Snapshot psiOneCell15Inputs_checked psiOneCell15Jets_checked
    corner_checked psiOneCell15Margin_checked p hp t ?_ ?_
  · have hanchor : ((4/32:ℚ):ℝ) = (((4:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor4_containsReal
  · change (((15:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((16:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell15_signed_wronskians

end Nuttall
