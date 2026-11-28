import Nuttall.PsiCompactCell32Margin
import Nuttall.PsiCompactCell32Jets
import Nuttall.PsiCompactUniformPanel9

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor9
      (fun j => (psiOneCell32Snapshot.jets j).asQInterval (2^90)) 36
      (9/32 - psiOneDyadicCenter 32)
    (psiOneCell32Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell32Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell32_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 32/128 ≤ t) (hU : t ≤ 33/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 32 9 (by decide) (by decide +kernel)
    psiOneCompactAnchor9 ?_ psiOneCell32Snapshot psiOneCell32Inputs_checked psiOneCell32Jets_checked
    corner_checked psiOneCell32Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor9_containsReal
  · change (32:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (33:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell32_signed_wronskians

end Nuttall
