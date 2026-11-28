import Nuttall.PsiCompactCell37Margin
import Nuttall.PsiCompactCell37Jets
import Nuttall.PsiCompactUniformPanel10

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor10
      (fun j => (psiOneCell37Snapshot.jets j).asQInterval (2^90)) 36
      (10/32 - psiOneDyadicCenter 37)
    (psiOneCell37Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell37Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell37_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 37/128 ≤ t) (hU : t ≤ 38/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 37 10 (by decide) (by decide +kernel)
    psiOneCompactAnchor10 ?_ psiOneCell37Snapshot psiOneCell37Inputs_checked psiOneCell37Jets_checked
    corner_checked psiOneCell37Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor10_containsReal
  · change (37:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (38:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell37_signed_wronskians

end Nuttall
