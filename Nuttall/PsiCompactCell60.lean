import Nuttall.PsiCompactCell60Margin
import Nuttall.PsiLastCellPanelCheck

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell60Inputs_checked :
    psiPreciseGridChecks (121/256) ∧
      psiPreciseGridInputs (121/256) = psiOneCell60GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell60PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell60PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell60GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell60PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell60PhiJet j).ContainsReal (iteratedDeriv j Phi ((121/256:ℚ):ℝ)) := by
  rw [cell60PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell60Inputs_checked.1 cell60Inputs_checked.2 j

private def cell60Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactHalfAnchor psiOneCell60PhiJet 36 (7/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell60Quadrature_checked :
    psiOneCell60Corner.lo ≤ cell60Quadrature.lo ∧ cell60Quadrature.hi ≤ psiOneCell60Corner.hi := by
  decide +kernel

theorem psiOneCell60Corner_containsReal :
    psiOneCell60Corner.ContainsReal (psi 1 ((121/256:ℚ):ℝ)) := by
  have hright : psiOneCompactHalfAnchor.ContainsReal
      (psi 1 (((121/256:ℚ):ℝ)+((7/256:ℚ):ℝ))) := by
    rw [show ((121/256:ℚ):ℝ)+((7/256:ℚ):ℝ) = (1/2:ℝ) by norm_num]
    exact psiOneCompactHalfAnchor_containsReal
  have hq : cell60Quadrature.ContainsReal (psi 1 ((121/256:ℚ):ℝ)) := by
    unfold cell60Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell60PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell60Quadrature_checked.1 cell60Quadrature_checked.2 hq

theorem psiOne_compact_cell60_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 15/32 ≤ t) (hU : t ≤ 61/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-121
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((121/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_fixed_jet_cell_signed_wronskians hp (121/256) (1/256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv 60
    psiOneCell60Corner_containsReal psiOneCell60PhiJet_containsReal psiOneCell60Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell60_signed_wronskians

end Nuttall
