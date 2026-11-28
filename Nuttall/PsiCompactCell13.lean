import Nuttall.PsiCompactCell13Margin
import Nuttall.PsiCompactCell13Jets
import Nuttall.PsiCompactUniformPanel4

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor4
      (fun j => (psiOneCell13Snapshot.jets j).asQInterval (2^90)) 36
      (4/32 - psiOneDyadicCenter 13)
    (psiOneCell13Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell13Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell13_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 13/128 ≤ t) (hU : t ≤ 14/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 13 4 (by decide) (by decide +kernel)
    psiOneCompactAnchor4 ?_ psiOneCell13Snapshot psiOneCell13Inputs_checked psiOneCell13Jets_checked
    corner_checked psiOneCell13Margin_checked p hp t ?_ ?_
  · have hanchor : ((4/32:ℚ):ℝ) = (((4:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor4_containsReal
  · change (((13:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((14:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell13_signed_wronskians

end Nuttall
