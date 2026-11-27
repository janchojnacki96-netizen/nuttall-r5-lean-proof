import Nuttall.PsiCompactSharedAnchors
import Nuttall.PsiTwoPanelBox

namespace Nuttall

open W5

/-- Ψ₂ enclosures at the same backwards anchors used for Ψ₁. -/
def psiTwoCompactAnchorFromPanels (panels : ℕ → QInterval) (jets : ℕ → ℕ → QInterval)
    (i : ℕ) : ℕ → QInterval
  | 0 => psiTwoPanelSeed
  | n+1 => psiTwoPanelBox
      (psiOneCompactAnchorFromPanels panels (i+1) n)
      (psiTwoCompactAnchorFromPanels panels jets (i+1) n) (jets i) (1/32)

theorem psiTwoCompactAnchorFromPanels_containsReal
    (panels : ℕ → QInterval) (jets : ℕ → ℕ → QInterval)
    (hjets : ∀ i < 22, ∀ j < 36, (jets i j).ContainsReal (iteratedDeriv j Phi ((i:ℝ)/32)))
    (hpanels : ∀ i < 22,
      let panel := psiOnePanelBox (QInterval.point 0) (jets i) 36 (1/32)
      (panels i).lo ≤ panel.lo ∧ panel.hi ≤ (panels i).hi)
    (i n : ℕ) (hend : i+n = 22) :
    (psiTwoCompactAnchorFromPanels panels jets i n).ContainsReal (psi 2 ((i:ℝ)/32)) := by
  induction n generalizing i with
  | zero =>
    have hi : i = 22 := by omega
    subst i
    simpa only [psiTwoCompactAnchorFromPanels, show ((22:ℕ):ℝ)/32 = 11/16 by norm_num]
      using psiTwoPanelSeed_containsReal
  | succ n ih =>
    have hi : i < 22 := by omega
    have hi' : (i:ℝ) < 22 := by exact_mod_cast hi
    have hnext : ((i+1:ℕ):ℝ)/32 = (i:ℝ)/32+((1/32:ℚ):ℝ) := by push_cast; ring
    have hone := psiOneCompactAnchorFromPanels_containsReal panels jets hjets hpanels
      (i+1) n (by omega)
    have htwo := ih (i+1) (by omega)
    rw [hnext] at hone htwo
    exact psiTwoPanelBox_containsReal (by positivity) (by norm_num)
      (by push_cast; linarith only [hi']) hone htwo (hjets i hi)

#print axioms psiTwoCompactAnchorFromPanels_containsReal

end Nuttall
