import Nuttall.PsiCompactCell48Margin
import Nuttall.PsiCompactUniformPanel13

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell48Inputs_checked :
    psiPreciseGridChecks (97/256) ∧
      psiPreciseGridInputs (97/256) = psiOneCell48GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell48PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell48PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell48GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell48PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell48PhiJet j).ContainsReal (iteratedDeriv j Phi ((97/256:ℚ):ℝ)) := by
  rw [cell48PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell48Inputs_checked.1 cell48Inputs_checked.2 j

private def cell48Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactAnchor13 psiOneCell48PhiJet 36 (7/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell48Quadrature_checked :
    psiOneCell48Corner.lo ≤ cell48Quadrature.lo ∧ cell48Quadrature.hi ≤ psiOneCell48Corner.hi := by
  decide +kernel

theorem psiOneCell48Corner_containsReal :
    psiOneCell48Corner.ContainsReal (psi 1 ((97/256:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor13.ContainsReal
      (psi 1 (((97/256:ℚ):ℝ)+((7/256:ℚ):ℝ))) := by
    rw [show ((97/256:ℚ):ℝ)+((7/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) by norm_num]
    exact psiOneCompactAnchor13_containsReal
  have hq : cell48Quadrature.ContainsReal (psi 1 ((97/256:ℚ):ℝ)) := by
    unfold cell48Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell48PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell48Quadrature_checked.1 cell48Quadrature_checked.2 hq

theorem psiOne_compact_cell48_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 3/8 ≤ t) (hU : t ≤ 49/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-97
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((97/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_dyadic_cell_signed_wronskians hp (c := ((97/256:ℚ):ℝ))
    (by norm_num) (by norm_num) hv 48
    psiOneCell48Corner_containsReal psiOneCell48PhiJet_containsReal psiOneCell48Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell48_signed_wronskians

end Nuttall
