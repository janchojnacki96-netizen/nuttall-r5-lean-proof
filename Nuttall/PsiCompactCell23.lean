import Nuttall.PsiCompactCell23Margin
import Nuttall.PsiCompactCell23Jets
import Nuttall.PsiCompactUniformPanel6

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor6
      (fun j => (psiOneCell23Snapshot.jets j).asQInterval (2^90)) 36
      (6/32 - psiOneDyadicCenter 23)
    (psiOneCell23Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell23Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell23_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 23/128 ≤ t) (hU : t ≤ 24/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 23 6 (by decide) (by decide +kernel)
    psiOneCompactAnchor6 ?_ psiOneCell23Snapshot psiOneCell23Inputs_checked psiOneCell23Jets_checked
    corner_checked psiOneCell23Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor6_containsReal
  · change (23:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (24:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell23_signed_wronskians

end Nuttall
