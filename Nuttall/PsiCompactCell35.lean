import Nuttall.PsiCompactCell35Margin
import Nuttall.PsiCompactCell35Jets
import Nuttall.PsiCompactUniformPanel9

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor9
      (fun j => (psiOneCell35Snapshot.jets j).asQInterval (2^90)) 36
      (9/32 - psiOneDyadicCenter 35)
    (psiOneCell35Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell35Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell35_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 35/128 ≤ t) (hU : t ≤ 36/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 35 9 (by decide) (by decide +kernel)
    psiOneCompactAnchor9 ?_ psiOneCell35Snapshot psiOneCell35Inputs_checked psiOneCell35Jets_checked
    corner_checked psiOneCell35Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor9_containsReal
  · change (35:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (36:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell35_signed_wronskians

end Nuttall
