import Nuttall.PsiCompactCell25Margin
import Nuttall.PsiCompactCell25Jets
import Nuttall.PsiCompactUniformPanel7

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor7
      (fun j => (psiOneCell25Snapshot.jets j).asQInterval (2^90)) 36
      (7/32 - psiOneDyadicCenter 25)
    (psiOneCell25Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell25Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell25_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 25/128 ≤ t) (hU : t ≤ 26/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 25 7 (by decide) (by decide +kernel)
    psiOneCompactAnchor7 ?_ psiOneCell25Snapshot psiOneCell25Inputs_checked psiOneCell25Jets_checked
    corner_checked psiOneCell25Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor7_containsReal
  · change (25:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (26:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell25_signed_wronskians

end Nuttall
