import Nuttall.PsiCompactCell29Margin
import Nuttall.PsiCompactCell29Jets
import Nuttall.PsiCompactUniformPanel8

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor8
      (fun j => (psiOneCell29Snapshot.jets j).asQInterval (2^90)) 36
      (8/32 - psiOneDyadicCenter 29)
    (psiOneCell29Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell29Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell29_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 29/128 ≤ t) (hU : t ≤ 30/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 29 8 (by decide) (by decide +kernel)
    psiOneCompactAnchor8 ?_ psiOneCell29Snapshot psiOneCell29Inputs_checked psiOneCell29Jets_checked
    corner_checked psiOneCell29Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor8_containsReal
  · change (29:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (30:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell29_signed_wronskians

end Nuttall
