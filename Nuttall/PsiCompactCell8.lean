import Nuttall.PsiCompactCell8Margin
import Nuttall.PsiCompactCell8Jets
import Nuttall.PsiCompactUniformPanel3

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor3
      (fun j => (psiOneCell8Snapshot.jets j).asQInterval (2^90)) 36
      (3/32 - psiOneDyadicCenter 8)
    (psiOneCell8Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell8Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell8_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 8/128 ≤ t) (hU : t ≤ 9/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 8 3 (by decide) (by decide +kernel)
    psiOneCompactAnchor3 ?_ psiOneCell8Snapshot psiOneCell8Inputs_checked psiOneCell8Jets_checked
    corner_checked psiOneCell8Margin_checked p hp t ?_ ?_
  · have hanchor : ((3/32:ℚ):ℝ) = (((3:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor3_containsReal
  · change (((8:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((9:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell8_signed_wronskians

end Nuttall
