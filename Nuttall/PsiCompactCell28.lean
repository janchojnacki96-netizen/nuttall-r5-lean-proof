import Nuttall.PsiCompactCell28Margin
import Nuttall.PsiCompactCell28Jets
import Nuttall.PsiCompactUniformPanel8

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor8
      (fun j => (psiOneCell28Snapshot.jets j).asQInterval (2^90)) 36
      (8/32 - psiOneDyadicCenter 28)
    (psiOneCell28Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell28Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell28_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 28/128 ≤ t) (hU : t ≤ 29/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 28 8 (by decide) (by decide +kernel)
    psiOneCompactAnchor8 ?_ psiOneCell28Snapshot psiOneCell28Inputs_checked psiOneCell28Jets_checked
    corner_checked psiOneCell28Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor8_containsReal
  · change (28:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (29:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell28_signed_wronskians

end Nuttall
