import Nuttall.PsiCompactSharedAnchors
import Nuttall.PsiFixedGridJets

namespace Nuttall

open W5

/-- One uniform panel advances a certified anchor to the grid point on its left. -/
theorem psiOne_compact_panel_step {i : ℕ} (hi : i < 22)
    {jets : ℕ → QInterval} {right panel : QInterval}
    (hright : right.ContainsReal (psi 1 (((i+1:ℕ):ℝ)/32)))
    (hjets : ∀ j < 36, (jets j).ContainsReal (iteratedDeriv j Phi ((i:ℝ)/32)))
    (hpanel : let raw := psiOnePanelBox (QInterval.point 0) jets 36 (1/32)
      panel.lo ≤ raw.lo ∧ raw.hi ≤ panel.hi) :
    (right.add panel).ContainsReal (psi 1 ((i:ℝ)/32)) := by
  have hnext : ((i+1:ℕ):ℝ)/32 = (i:ℝ)/32+((1/32:ℚ):ℝ) := by push_cast; ring
  have hir : (i:ℝ) ≤ 22 := by exact_mod_cast hi.le
  rw [hnext] at hright
  have h := psiOnePanelBox_containsReal (by positivity) (by norm_num)
    (by push_cast; linarith only [hir]) hright (fun j hj => hjets j (Finset.mem_range.mp hj))
  rw [psiOnePanelBox_eq_add_zero] at h
  exact compactContainsReal_of_endpoints (add_le_add (le_refl _) hpanel.1)
    (add_le_add (le_refl _) hpanel.2) h

#print axioms psiOne_compact_panel_step

end Nuttall
