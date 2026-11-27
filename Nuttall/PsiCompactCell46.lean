import Nuttall.PsiCompactCell46Margin
import Nuttall.PsiCompactCell46Jets
import Nuttall.PsiCompactUniformPanel12

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor12
      (fun j => (psiOneCell46Snapshot.jets j).asQInterval (2^90)) 36
      (12/32 - psiOneDyadicCenter 46)
    (psiOneCell46Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell46Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell46_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 46/128 ≤ t) (hU : t ≤ 47/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 46 12 (by decide) (by decide +kernel)
    psiOneCompactAnchor12 ?_ psiOneCell46Snapshot psiOneCell46Inputs_checked psiOneCell46Jets_checked
    corner_checked psiOneCell46Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor12_containsReal
  · change (46:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (47:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell46_signed_wronskians

end Nuttall
