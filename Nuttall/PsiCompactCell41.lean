import Nuttall.PsiCompactCell41Margin
import Nuttall.PsiCompactCell41Jets
import Nuttall.PsiCompactUniformPanel11

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor11
      (fun j => (psiOneCell41Snapshot.jets j).asQInterval (2^90)) 36
      (11/32 - psiOneDyadicCenter 41)
    (psiOneCell41Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell41Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell41_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 41/128 ≤ t) (hU : t ≤ 42/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 41 11 (by decide) (by decide +kernel)
    psiOneCompactAnchor11 ?_ psiOneCell41Snapshot psiOneCell41Inputs_checked psiOneCell41Jets_checked
    corner_checked psiOneCell41Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor11_containsReal
  · change (41:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (42:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell41_signed_wronskians

end Nuttall
