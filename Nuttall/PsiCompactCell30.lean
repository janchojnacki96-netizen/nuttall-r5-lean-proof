import Nuttall.PsiCompactCell30Margin
import Nuttall.PsiCompactCell30Jets
import Nuttall.PsiCompactUniformPanel8

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor8
      (fun j => (psiOneCell30Snapshot.jets j).asQInterval (2^90)) 36
      (8/32 - psiOneDyadicCenter 30)
    (psiOneCell30Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell30Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell30_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 30/128 ≤ t) (hU : t ≤ 31/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 30 8 (by decide) (by decide +kernel)
    psiOneCompactAnchor8 ?_ psiOneCell30Snapshot psiOneCell30Inputs_checked psiOneCell30Jets_checked
    corner_checked psiOneCell30Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor8_containsReal
  · change (30:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (31:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell30_signed_wronskians

end Nuttall
