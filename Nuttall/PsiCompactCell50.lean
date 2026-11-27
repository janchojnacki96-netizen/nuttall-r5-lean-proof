import Nuttall.PsiCompactCell50Margin
import Nuttall.PsiCompactUniformPanel13

namespace Nuttall

open W5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell50Inputs_checked :
    psiPreciseGridChecks (101/256) ∧
      psiPreciseGridInputs (101/256) = psiOneCell50GridInputs := by
  decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell50PhiJet_checked (j : ℕ) (hj : j < 36) :
    psiOneCell50PhiJet j = psiFixedGridPhiJetBoxOfInputs psiOneCell50GridInputs j := by
  interval_cases j <;> decide +kernel

theorem psiOneCell50PhiJet_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneCell50PhiJet j).ContainsReal (iteratedDeriv j Phi ((101/256:ℚ):ℝ)) := by
  rw [cell50PhiJet_checked j hj]
  exact psiFixedGridPhiJetBoxOfInputs_containsReal (by norm_num) (by norm_num)
    cell50Inputs_checked.1 cell50Inputs_checked.2 j

private def cell50Quadrature : QInterval :=
  psiOnePanelBox psiOneCompactAnchor13 psiOneCell50PhiJet 36 (3/256)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem cell50Quadrature_checked :
    psiOneCell50Corner.lo ≤ cell50Quadrature.lo ∧ cell50Quadrature.hi ≤ psiOneCell50Corner.hi := by
  decide +kernel

theorem psiOneCell50Corner_containsReal :
    psiOneCell50Corner.ContainsReal (psi 1 ((101/256:ℚ):ℝ)) := by
  have hright : psiOneCompactAnchor13.ContainsReal
      (psi 1 (((101/256:ℚ):ℝ)+((3/256:ℚ):ℝ))) := by
    rw [show ((101/256:ℚ):ℝ)+((3/256:ℚ):ℝ) = ((13/32:ℚ):ℝ) by norm_num]
    exact psiOneCompactAnchor13_containsReal
  have hq : cell50Quadrature.ContainsReal (psi 1 ((101/256:ℚ):ℝ)) := by
    unfold cell50Quadrature
    exact psiOnePanelBox_containsReal (by norm_num) (by norm_num) (by norm_num) hright
      (fun j hj => psiOneCell50PhiJet_containsReal j (Finset.mem_range.mp hj))
  exact compactContainsReal_of_endpoints cell50Quadrature_checked.1 cell50Quadrature_checked.2 hq

theorem psiOne_compact_cell50_signed_wronskians (p : ℕ) (hp : p ≤ 7)
    (t : ℝ) (hL : 25/64 ≤ t) (hU : t ≤ 51/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  let v := 256*t-101
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hL],
    by dsimp [v]; linarith only [hU]⟩
  have ht : ((101/256:ℚ):ℝ)+((1/256:ℚ):ℝ)*v = t := by
    dsimp [v]
    push_cast
    ring
  have h := psiOne_compact_dyadic_cell_signed_wronskians hp (c := ((101/256:ℚ):ℝ))
    (by norm_num) (by norm_num) hv 50
    psiOneCell50Corner_containsReal psiOneCell50PhiJet_containsReal psiOneCell50Margin_checked
  rwa [ht] at h

#print axioms psiOne_compact_cell50_signed_wronskians

end Nuttall
