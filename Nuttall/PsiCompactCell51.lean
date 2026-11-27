import Nuttall.PsiCompactCell51Margin
import Nuttall.PsiCompactUniformPanel13

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell51Inputs_checked :
    psiPreciseGridChecks (103/256) ∧
      psiPreciseGridInputs (103/256) = psiOneCell51GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell51PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell51PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell51GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell51PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell51PhiJet j).ContainsReal (iteratedDeriv j Phi ((103/256:ℚ):ℝ)) := by
  rw [cell51PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell51Inputs_checked.1 cell51Inputs_checked.2 j

private def cell51Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactAnchor13 psiOneCell51PhiJet 36 (1/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell51Quadrature_checked :
    psiOneCell51Corner.lo ≤ cell51Quadrature.lo ∧ cell51Quadrature.hi ≤ psiOneCell51Corner.hi := by
  decide +kernel

theorem psiOneCell51Corner_containsReal :
    psiOneCell51Corner.ContainsReal (psi 1 ((103/256:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor13.ContainsReal
      (psi 1 (((103/256:ℚ):ℝ)+((1/256:ℚ):ℝ))) := by
    rw [show ((103/256:ℚ):ℝ)+((1/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) by norm_num]
    exact psiOneCompactAnchor13_containsReal
  have hq : cell51Quadrature.ContainsReal (psi 1 ((103/256:ℚ):ℝ)) := by
    unfold cell51Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell51PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell51Quadrature_checked.1 cell51Quadrature_checked.2 hq

theorem psiOne_compact_cell51_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 51/128 ≤ t) (hU : t ≤ 13/32) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-103
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((103/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_dyadic_cell_signed_wronskians hp (c := ((103/256:ℚ):ℝ))
    (by norm_num) (by norm_num) hv 51
    psiOneCell51Corner_containsReal psiOneCell51PhiJet_containsReal psiOneCell51Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell51_signed_wronskians

end Nuttall
