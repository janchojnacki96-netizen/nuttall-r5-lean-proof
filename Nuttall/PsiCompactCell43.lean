import Nuttall.PsiCompactCell43Margin
import Nuttall.PsiCompactCell43Jets
import Nuttall.PsiCompactUniformPanel11

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor11
      (fun j => (psiOneCell43Snapshot.jets j).asQInterval (2^90)) 36
      (11/32 - psiOneDyadicCenter 43)
    (psiOneCell43Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell43Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell43_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 43/128 ≤ t) (hU : t ≤ 44/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 43 11 (by decide) (by decide +kernel)
    psiOneCompactAnchor11 ?_ psiOneCell43Snapshot psiOneCell43Inputs_checked psiOneCell43Jets_checked
    corner_checked psiOneCell43Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor11_containsReal
  · change (43:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (44:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell43_signed_wronskians

end Nuttall
