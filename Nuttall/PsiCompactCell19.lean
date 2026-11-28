import Nuttall.PsiCompactCell19Margin
import Nuttall.PsiCompactCell19Jets
import Nuttall.PsiCompactUniformPanel5

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor5
      (fun j => (psiOneCell19Snapshot.jets j).asQInterval (2^90)) 36
      (5/32 - psiOneDyadicCenter 19)
    (psiOneCell19Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell19Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell19_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 19/128 ≤ t) (hU : t ≤ 20/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 19 5 (by decide) (by decide +kernel)
    psiOneCompactAnchor5 ?_ psiOneCell19Snapshot psiOneCell19Inputs_checked psiOneCell19Jets_checked
    corner_checked psiOneCell19Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor5_containsReal
  · change (19:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (20:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell19_signed_wronskians

end Nuttall
