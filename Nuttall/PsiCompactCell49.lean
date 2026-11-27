import Nuttall.PsiCompactCell49Margin
import Nuttall.PsiCompactUniformPanel13

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell49Inputs_checked :
    psiPreciseGridChecks (99/256) ∧
      psiPreciseGridInputs (99/256) = psiOneCell49GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell49PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell49PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell49GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell49PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell49PhiJet j).ContainsReal (iteratedDeriv j Phi ((99/256:ℚ):ℝ)) := by
  rw [cell49PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell49Inputs_checked.1 cell49Inputs_checked.2 j

private def cell49Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactAnchor13 psiOneCell49PhiJet 36 (5/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell49Quadrature_checked :
    psiOneCell49Corner.lo ≤ cell49Quadrature.lo ∧ cell49Quadrature.hi ≤ psiOneCell49Corner.hi := by
  decide +kernel

theorem psiOneCell49Corner_containsReal :
    psiOneCell49Corner.ContainsReal (psi 1 ((99/256:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor13.ContainsReal
      (psi 1 (((99/256:ℚ):ℝ)+((5/256:ℚ):ℝ))) := by
    rw [show ((99/256:ℚ):ℝ)+((5/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) by norm_num]
    exact psiOneCompactAnchor13_containsReal
  have hq : cell49Quadrature.ContainsReal (psi 1 ((99/256:ℚ):ℝ)) := by
    unfold cell49Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell49PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell49Quadrature_checked.1 cell49Quadrature_checked.2 hq

theorem psiOne_compact_cell49_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 49/128 ≤ t) (hU : t ≤ 25/64) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-99
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((99/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_dyadic_cell_signed_wronskians hp (c := ((99/256:ℚ):ℝ))
    (by norm_num) (by norm_num) hv 49
    psiOneCell49Corner_containsReal psiOneCell49PhiJet_containsReal psiOneCell49Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell49_signed_wronskians

end Nuttall
