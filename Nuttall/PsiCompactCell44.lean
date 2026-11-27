import Nuttall.PsiCompactCell44Margin
import Nuttall.PsiCompactUniformPanel12

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem input_checked :
    psiPreciseGridChecks (psiOneDyadicCenter 44) ∧
      psiPreciseGridInputs (psiOneDyadicCenter 44) = psiOneCell44Snapshot.input := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem jets_checked (j : ℕ) (hj : j < 36) :
    (psiOneCell44Snapshot.jets j).asQInterval (2^90) =
      psiFixedGridPhiJetBoxOfInputs psiOneCell44Snapshot.input j := by
  interval_cases j <;> decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem corner_checked :
    let raw := psiOnePanelBox psiOneCompactAnchor12
      (fun j => (psiOneCell44Snapshot.jets j).asQInterval (2^90)) 36
      (12/32 - psiOneDyadicCenter 44)
    (psiOneCell44Snapshot.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
      raw.hi ≤ (psiOneCell44Snapshot.corner.asQInterval (2^90)).hi := by
  decide +kernel

theorem psiOne_compact_cell44_signed_wronskians (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hL : 44/128 ≤ t) (hU : t ≤ 45/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_dyadic_snapshot_sound 44 12 (by decide) (by decide +kernel)
    psiOneCompactAnchor12 ?_ psiOneCell44Snapshot input_checked jets_checked
    corner_checked psiOneCell44Margin_checked p hp t ?_ ?_
  · simpa only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] using
      psiOneCompactAnchor12_containsReal
  · change (44:ℝ)/128 ≤ t
    exact hL
  · change t ≤ (45:ℝ)/128
    exact hU

#print axioms psiOne_compact_cell44_signed_wronskians

end Nuttall
