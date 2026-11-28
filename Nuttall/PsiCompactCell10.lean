import Nuttall.PsiCompactCell10Margin
import Nuttall.PsiCompactCell10Jets
import Nuttall.PsiCompactUniformPanel3

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor3
      (fun j => (psiOneCell10Snapshot.jets j).asQInterval (2^90)) 36
      (3/32 - psiOneDyadicCenter 10)
    (psiOneCell10Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell10Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell10_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 10/128 ≤ t) (hU : t ≤ 11/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 10 3 (by decide) (by decide +kernel)
    psiOneCompactAnchor3 ?_ psiOneCell10Snapshot psiOneCell10Inputs_checked psiOneCell10Jets_checked
    corner_checked psiOneCell10Margin_checked p hp t ?_ ?_
  · have hanchor : ((3/32:ℚ):ℝ) = (((3:ℕ):ℝ)/32) := by norm_num
    rw [← hanchor]
    exact psiOneCompactAnchor3_containsReal
  · change (((10:ℕ):ℝ)/128) ≤ t
    norm_num at hL ⊢
    exact hL
  · change t ≤ (((11:ℕ):ℝ)/128)
    norm_num at hU ⊢
    exact hU

#print axioms psiOne_compact_cell10_signed_wronskians

end Nuttall
