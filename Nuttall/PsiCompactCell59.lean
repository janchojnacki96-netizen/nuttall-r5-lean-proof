import Nuttall.PsiCompactCell59Margin
import Nuttall.PsiCompactUniformPanel15

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell59Inputs_checked :
    psiPreciseGridChecks (119/256) ∧
      psiPreciseGridInputs (119/256) = psiOneCell59GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell59PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell59PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell59GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell59PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell59PhiJet j).ContainsReal (iteratedDeriv j Phi ((119/256:ℚ):ℝ)) := by
  rw [cell59PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell59Inputs_checked.1 cell59Inputs_checked.2 j

private def cell59Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactFifteen32Anchor psiOneCell59PhiJet 36 (1/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell59Quadrature_checked :
    psiOneCell59Corner.lo ≤ cell59Quadrature.lo ∧ cell59Quadrature.hi ≤ psiOneCell59Corner.hi := by
  decide +kernel

theorem psiOneCell59Corner_containsReal :
    psiOneCell59Corner.ContainsReal (psi 1 ((119/256:ℚ):ℝ)) := by
  have hright : psiOneCompactFifteen32Anchor.ContainsReal
      (psi 1 (((119/256:ℚ):ℝ)+((1/256:ℚ):ℝ))) := by
    rw [show ((119/256:ℚ):ℝ)+((1/256:ℚ):ℝ) = ((15/32:ℚ):ℝ) by norm_num]
    exact psiOneCompactFifteen32Anchor_containsReal
  have hq : cell59Quadrature.ContainsReal (psi 1 ((119/256:ℚ):ℝ)) := by
    unfold cell59Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell59PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell59Quadrature_checked.1 cell59Quadrature_checked.2 hq

theorem psiOne_compact_cell59_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 59/128 ≤ t) (hU : t ≤ 15/32) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-119
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((119/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_fixed_jet_cell_signed_wronskians hp (119/256) (1/256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv 59
    psiOneCell59Corner_containsReal psiOneCell59PhiJet_containsReal psiOneCell59Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell59_signed_wronskians

end Nuttall
