import Nuttall.PsiTwoPanelTaylor
import Nuttall.PsiCompactQuadrature

namespace Nuttall

open W5
open scoped BigOperators

private def psiTwoPanelWeight (h : ℚ) (j : ℕ) : ℚ :=
  h^(j+2) / (((j:ℚ)+2) * (j.factorial:ℚ))

/-- A weighted quadrature enclosure, with both right endpoint values supplied. -/
def psiTwoPanelBox (one two : QInterval) (jets : ℕ → QInterval) (h : ℚ) : QInterval :=
  let base := two.add ((QInterval.point h).mul one)
  let correction := QInterval.sumBox (Finset.range 36) fun j =>
    (QInterval.point (psiTwoPanelWeight h j)).mul (jets j)
  let err := (8:ℚ)^36 * 10^6 * h^38 / 38
  (base.add correction).add ⟨-err, err⟩

theorem psiTwoPanelBox_containsReal {one two : QInterval} {jets : ℕ → QInterval}
    {a : ℝ} {h : ℚ} (ha : 0 ≤ a) (hh : 0 ≤ h) (hb : a+(h:ℝ) ≤ 2)
    (hone : one.ContainsReal (psi 1 (a+(h:ℝ))))
    (htwo : two.ContainsReal (psi 2 (a+(h:ℝ))))
    (hjets : ∀ j < 36, (jets j).ContainsReal (iteratedDeriv j Phi a)) :
    (psiTwoPanelBox one two jets h).ContainsReal (psi 2 a) := by
  let predicted := psi 2 (a+(h:ℝ)) + (h:ℝ) * psi 1 (a+(h:ℝ)) +
    psiTwoPanelCorrection 36 a (h:ℝ)
  have hbase := QInterval.add_containsReal htwo
    (QInterval.mul_containsReal
      (show (QInterval.point h).ContainsReal (h:ℝ) by simp [QInterval.ContainsReal, QInterval.point])
      hone)
  have hpoly : (QInterval.sumBox (Finset.range 36) (fun j =>
      (QInterval.point (psiTwoPanelWeight h j)).mul (jets j))).ContainsReal
      (psiTwoPanelCorrection 36 a (h:ℝ)) := by
    unfold psiTwoPanelCorrection
    apply QInterval.sumBox_containsReal
    intro j hj
    have hweight : (QInterval.point (psiTwoPanelWeight h j)).ContainsReal
        ((h:ℝ)^(j+2) / (((j:ℝ)+2) * (j.factorial:ℝ))) := by
      simp [QInterval.ContainsReal, QInterval.point, psiTwoPanelWeight]
    simpa only [mul_comm, mul_div_assoc] using
      (QInterval.mul_containsReal hweight (hjets j (Finset.mem_range.mp hj)))
  have herr := psi_two_panel_error_le ha (by exact_mod_cast hh) hb
  have herrBox : (⟨-((8:ℚ)^36 * 10^6 * h^38 / 38), (8:ℚ)^36 * 10^6 * h^38 / 38⟩ :
        QInterval).ContainsReal (psi 2 a - predicted) := by
    simpa [QInterval.ContainsReal, predicted] using abs_le.mp herr
  have htotal := QInterval.add_containsReal (QInterval.add_containsReal hbase hpoly) herrBox
  change (psiTwoPanelBox one two jets h).ContainsReal (predicted + (psi 2 a-predicted)) at htotal
  rwa [show predicted + (psi 2 a-predicted) = psi 2 a by ring] at htotal

/-- Right seed intervals for both quadratures. -/
def psiTwoPanelSeed : QInterval := ⟨0, 1/10^16⟩

theorem psiTwoPanelSeed_containsReal : psiTwoPanelSeed.ContainsReal (psi 2 (11/16)) := by
  simpa [psiTwoPanelSeed, QInterval.ContainsReal] using psi_two_precise_compact_seed_bounds

#print axioms psiTwoPanelBox_containsReal
#print axioms psiTwoPanelSeed_containsReal

end Nuttall
