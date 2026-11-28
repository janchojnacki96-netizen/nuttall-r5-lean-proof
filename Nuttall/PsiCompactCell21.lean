import Nuttall.PsiCompactCell21Margin
import Nuttall.PsiCompactCell21Jets
import Nuttall.PsiCompactUniformPanel6

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor6
      (fun j => (psiOneCell21Snapshot.jets j).asQInterval (2^90)) 36
      (6/32 - psiOneDyadicCenter 21)
    (psiOneCell21Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell21Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell21_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 21/128 ≤ t) (hU : t ≤ 22/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 21 6 (by decide) (by decide +kernel)
    psiOneCompactAnchor6 ?_ psiOneCell21Snapshot psiOneCell21Inputs_checked psiOneCell21Jets_checked
    corner_checked psiOneCell21Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor6_containsReal
  · change (21:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (22:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell21_signed_wronskians

end Nuttall
