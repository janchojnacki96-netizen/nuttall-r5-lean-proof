import Nuttall.PsiCompactCell14Margin
import Nuttall.PsiCompactCell14Jets
import Nuttall.PsiCompactUniformPanel4

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor4
      (fun j => (psiOneCell14Snapshot.jets j).asQInterval (2^90)) 36
      (4/32 - psiOneDyadicCenter 14)
    (psiOneCell14Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell14Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell14_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 14/128 ≤ t) (hU : t ≤ 15/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 14 4 (by decide) (by decide +kernel)
    psiOneCompactAnchor4 ?_ psiOneCell14Snapshot psiOneCell14Inputs_checked psiOneCell14Jets_checked
    corner_checked psiOneCell14Margin_checked p hp t ?_ ?_
  · have hanchor : ((4/32:ℚ):ℝ) = (((4:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor4_containsReal
  · change (((14:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((15:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell14_signed_wronskians

end Nuttall
