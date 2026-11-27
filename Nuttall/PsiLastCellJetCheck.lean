import Nuttall.PsiLastCellGridInputs
import Nuttall.PsiLastCellJetData

namespace Nuttall

open W5

private def lastCellJetCheck (j : ℕ) : Prop :=
  (psiOneLastCellJetSnapshot j).lo ≤
      (psiPreciseGridPhiJetBoxOfInputs (psiLastCellGridInputs 0) j).neg.lo ∧
    (psiPreciseGridPhiJetBoxOfInputs (psiLastCellGridInputs 0) j).neg.hi ≤
      (psiOneLastCellJetSnapshot j).hi

private instance (j : ℕ) : Decidable (lastCellJetCheck j) := by
  unfold lastCellJetCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem lastCellJetCheck_of_lt (j : ℕ) (hj : j < 36) : lastCellJetCheck j := by
  interval_cases j <;> decide +kernel

theorem psiOneLastCellJetSnapshot_containsReal (j : ℕ) (hj : j < 36) :
    (psiOneLastCellJetSnapshot j).ContainsReal (iteratedDeriv (j+1) (psi 1) (255/512)) := by
  have ht : psiLastCellNode 0 = 255/512 := by decide +kernel
  have hc := psiLastCellGridInputs_checked 0
  have h := psiPreciseGridPhiJetBox_containsReal
    (t := psiLastCellNode 0) (by rw [ht]; norm_num) (by rw [ht]; norm_num) hc.1 j
  rw [psiPreciseGridPhiJetBox, hc.2, ht] at h
  simp only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [show (1:ℕ) = 0+1 by rfl, iteratedDeriv_succ_psi_succ]
  exact compactContainsReal_of_endpoints (lastCellJetCheck_of_lt j hj).1
    (lastCellJetCheck_of_lt j hj).2 (QInterval.neg_containsReal h)

#print axioms psiOneLastCellJetSnapshot_containsReal

end Nuttall
