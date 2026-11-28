import Nuttall.PsiCompactCell39Margin
import Nuttall.PsiCompactCell39Jets
import Nuttall.PsiCompactUniformPanel10

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor10
      (fun j => (psiOneCell39Snapshot.jets j).asQInterval (2^90)) 36
      (10/32 - psiOneDyadicCenter 39)
    (psiOneCell39Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell39Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell39_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 39/128 ≤ t) (hU : t ≤ 40/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 39 10 (by decide) (by decide +kernel)
    psiOneCompactAnchor10 ?_ psiOneCell39Snapshot psiOneCell39Inputs_checked psiOneCell39Jets_checked
    corner_checked psiOneCell39Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor10_containsReal
  · change (39:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (40:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell39_signed_wronskians

end Nuttall
