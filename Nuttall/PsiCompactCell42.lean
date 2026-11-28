import Nuttall.PsiCompactCell42Margin
import Nuttall.PsiCompactCell42Jets
import Nuttall.PsiCompactUniformPanel11

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor11
      (fun j => (psiOneCell42Snapshot.jets j).asQInterval (2^90)) 36
      (11/32 - psiOneDyadicCenter 42)
    (psiOneCell42Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell42Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell42_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 42/128 ≤ t) (hU : t ≤ 43/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 42 11 (by decide) (by decide +kernel)
    psiOneCompactAnchor11 ?_ psiOneCell42Snapshot psiOneCell42Inputs_checked psiOneCell42Jets_checked
    corner_checked psiOneCell42Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor11_containsReal
  · change (42:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (43:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell42_signed_wronskians

end Nuttall
