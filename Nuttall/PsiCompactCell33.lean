import Nuttall.PsiCompactCell33Margin
import Nuttall.PsiCompactCell33Jets
import Nuttall.PsiCompactUniformPanel9

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor9
      (fun j => (psiOneCell33Snapshot.jets j).asQInterval (2^90)) 36
      (9/32 - psiOneDyadicCenter 33)
    (psiOneCell33Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell33Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell33_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 33/128 ≤ t) (hU : t ≤ 34/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 33 9 (by decide) (by decide +kernel)
    psiOneCompactAnchor9 ?_ psiOneCell33Snapshot psiOneCell33Inputs_checked psiOneCell33Jets_checked
    corner_checked psiOneCell33Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor9_containsReal
  · change (33:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (34:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell33_signed_wronskians

end Nuttall
