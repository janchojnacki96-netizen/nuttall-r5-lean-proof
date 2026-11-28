import Nuttall.PsiCompactCell34Margin
import Nuttall.PsiCompactCell34Jets
import Nuttall.PsiCompactUniformPanel9

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor9
      (fun j => (psiOneCell34Snapshot.jets j).asQInterval (2^90)) 36
      (9/32 - psiOneDyadicCenter 34)
    (psiOneCell34Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell34Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell34_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 34/128 ≤ t) (hU : t ≤ 35/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 34 9 (by decide) (by decide +kernel)
    psiOneCompactAnchor9 ?_ psiOneCell34Snapshot psiOneCell34Inputs_checked psiOneCell34Jets_checked
    corner_checked psiOneCell34Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor9_containsReal
  · change (34:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (35:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell34_signed_wronskians

end Nuttall
