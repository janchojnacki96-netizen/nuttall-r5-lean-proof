import Nuttall.PsiCompactPrecisionSeed
import Nuttall.PsiCompactQuadrature

namespace Nuttall

open W5

/-- Sum the panel enclosures to the left of the anchor at 22/32. -/
def psiOneCompactAnchorFromPanels (panels : ℕ → QInterval) (i : ℕ) : ℕ → QInterval
  | 0 => ⟨0, 1/10^16⟩
  | n+1 => (psiOneCompactAnchorFromPanels panels (i+1) n).add (panels i)

theorem psiOneCompactAnchorFromPanels_containsReal
    (panels : ℕ → QInterval) (jets : ℕ → ℕ → QInterval)
    (hjets : ∀ i < 22, ∀ j < 36, (jets i j).ContainsReal (iteratedDeriv j Phi ((i:ℝ)/32)))
    (hpanels : ∀ i < 22,
      let panel := psiOnePanelBox (QInterval.point 0) (jets i) 36 (1/32)
      (panels i).lo ≤ panel.lo ∧ panel.hi ≤ (panels i).hi)
    (i n : ℕ) (hend : i+n = 22) :
    (psiOneCompactAnchorFromPanels panels i n).ContainsReal (psi 1 ((i:ℝ)/32)) := by
  induction n generalizing i with
  | zero =>
    have hi : i = 22 := by omega
    subst i
    simpa only [psiOneCompactAnchorFromPanels, QInterval.ContainsReal, Nat.cast_ofNat,
      Rat.cast_div, Rat.cast_pow, Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat]
      using psi_one_precise_compact_seed_bounds (t := (22:ℝ)/32) (by norm_num) (by norm_num)
  | succ n ih =>
    have hi : i < 22 := by omega
    have hi' : (i:ℝ) < 22 := by exact_mod_cast hi
    have hnext : ((i+1:ℕ):ℝ)/32 = (i:ℝ)/32+((1/32:ℚ):ℝ) := by push_cast; ring
    have hprev := ih (i+1) (by omega)
    rw [hnext] at hprev
    have h := psiOnePanelBox_containsReal (d := 36) (h := (1:ℚ)/32)
      (by positivity) (by norm_num) (by push_cast; linarith only [hi']) hprev
      (fun j hj => hjets i hi j (Finset.mem_range.mp hj))
    rw [psiOnePanelBox_eq_add_zero] at h
    exact compactContainsReal_of_endpoints (add_le_add_left (hpanels i hi).1 _)
      (add_le_add_left (hpanels i hi).2 _) h

/-- A short panel reuses the jets at its center and a shared uniform anchor. -/
theorem psiOneCompactShortPanel_containsReal {center : ℚ} {anchor : ℕ} {right : QInterval}
    {jets : ℕ → QInterval} (hc : 0 ≤ center) (hca : center ≤ (anchor:ℚ)/32)
    (ha : anchor ≤ 22) (hright : right.ContainsReal (psi 1 ((anchor:ℝ)/32)))
    (hjets : ∀ j < 36, (jets j).ContainsReal (iteratedDeriv j Phi (center:ℝ))) :
    (psiOnePanelBox right jets 36 ((anchor:ℚ)/32-center)).ContainsReal (psi 1 (center:ℝ)) := by
  have ha' : (anchor:ℝ) ≤ 22 := by exact_mod_cast ha
  have he : (center:ℝ) + ((((anchor:ℚ)/32-center):ℚ):ℝ) = (anchor:ℝ)/32 := by
    push_cast
    ring
  exact psiOnePanelBox_containsReal (by exact_mod_cast hc) (sub_nonneg.mpr hca)
    (by rw [he]; linarith only [ha']) (by rwa [he])
    (fun j hj => hjets j (Finset.mem_range.mp hj))

#print axioms psiOneCompactAnchorFromPanels_containsReal
#print axioms psiOneCompactShortPanel_containsReal

end Nuttall
