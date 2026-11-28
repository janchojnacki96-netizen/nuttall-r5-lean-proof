import Nuttall.PsiCompactCell27Margin
import Nuttall.PsiCompactCell27Jets
import Nuttall.PsiCompactUniformPanel7

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor7
      (fun j => (psiOneCell27Snapshot.jets j).asQInterval (2^90)) 36
      (7/32 - psiOneDyadicCenter 27)
    (psiOneCell27Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell27Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell27_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 27/128 ≤ t) (hU : t ≤ 28/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 27 7 (by decide) (by decide +kernel)
    psiOneCompactAnchor7 ?_ psiOneCell27Snapshot psiOneCell27Inputs_checked psiOneCell27Jets_checked
    corner_checked psiOneCell27Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor7_containsReal
  · change (27:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (28:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell27_signed_wronskians

end Nuttall
