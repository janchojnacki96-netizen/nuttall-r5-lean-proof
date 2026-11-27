import Nuttall.PsiCompactCell52Margin
import Nuttall.PsiCompactUniformPanel14

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell52Inputs_checked :
    psiPreciseGridChecks (105/256) ∧
      psiPreciseGridInputs (105/256) = psiOneCell52GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell52PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell52PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell52GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell52PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell52PhiJet j).ContainsReal (iteratedDeriv j Phi ((105/256:ℚ):ℝ)) := by
  rw [cell52PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell52Inputs_checked.1 cell52Inputs_checked.2 j

private def cell52Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactAnchor14 psiOneCell52PhiJet 36 (7/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell52Quadrature_checked :
    psiOneCell52Corner.lo ≤ cell52Quadrature.lo ∧ cell52Quadrature.hi ≤ psiOneCell52Corner.hi := by
  decide +kernel

theorem psiOneCell52Corner_containsReal :
    psiOneCell52Corner.ContainsReal (psi 1 ((105/256:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor14.ContainsReal
      (psi 1 (((105/256:ℚ):ℝ)+((7/256:ℚ):ℝ))) := by
    rw [show ((105/256:ℚ):ℝ)+((7/256:ℚ):ℝ) = ((14/32:ℚ):ℝ) by norm_num]
    exact psiOneCompactAnchor14_containsReal
  have hq : cell52Quadrature.ContainsReal (psi 1 ((105/256:ℚ):ℝ)) := by
    unfold cell52Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell52PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell52Quadrature_checked.1 cell52Quadrature_checked.2 hq

theorem psiOne_compact_cell52_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 13/32 ≤ t) (hU : t ≤ 53/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-105
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((105/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_fixed_jet_cell_signed_wronskians hp (105/256) (1/256)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hv 52
    psiOneCell52Corner_containsReal psiOneCell52PhiJet_containsReal psiOneCell52Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell52_signed_wronskians

end Nuttall
