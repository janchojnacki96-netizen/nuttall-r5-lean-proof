import Nuttall.PsiCompactCell40Margin
import Nuttall.PsiCompactCell40Jets
import Nuttall.PsiCompactUniformPanel11

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor11
      (fun j => (psiOneCell40Snapshot.jets j).asQInterval (2^90)) 36
      (11/32 - psiOneDyadicCenter 40)
    (psiOneCell40Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell40Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell40_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 40/128 ≤ t) (hU : t ≤ 41/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 40 11 (by decide) (by decide +kernel)
    psiOneCompactAnchor11 ?_ psiOneCell40Snapshot psiOneCell40Inputs_checked psiOneCell40Jets_checked
    corner_checked psiOneCell40Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor11_containsReal
  · change (40:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (41:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell40_signed_wronskians

end Nuttall
