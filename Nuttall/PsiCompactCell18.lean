import Nuttall.PsiCompactCell18Margin
import Nuttall.PsiCompactCell18Jets
import Nuttall.PsiCompactUniformPanel5

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor5
      (fun j => (psiOneCell18Snapshot.jets j).asQInterval (2^90)) 36
      (5/32 - psiOneDyadicCenter 18)
    (psiOneCell18Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell18Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell18_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 18/128 ≤ t) (hU : t ≤ 19/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 18 5 (by decide) (by decide +kernel)
    psiOneCompactAnchor5 ?_ psiOneCell18Snapshot psiOneCell18Inputs_checked psiOneCell18Jets_checked
    corner_checked psiOneCell18Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor5_containsReal
  · change (18:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (19:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell18_signed_wronskians

end Nuttall
