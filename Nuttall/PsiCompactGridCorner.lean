import Nuttall.PsiCompactPrecisionSeed
import Nuttall.PsiPreciseGridJets

namespace Nuttall

open W5

private def compactAnchorBox : QInterval := ⟨0, 1/10^16⟩

private def compactGridJet (c : ℚ) (i j : ℕ) : QInterval :=
  psiPreciseGridPhiJetBox (c+(i:ℚ)/32) j

/-- A grid of order-36 Taylor panels from the specified start to the
right anchor, which must lie between 11/16 and 1. -/
def psiOneCompactAnchorBox (c : ℚ) (panels : ℕ) : QInterval :=
  psiOneUniformGridBox compactAnchorBox (compactGridJet c) 36 (1/32) 0 panels

theorem psiOneCompactAnchorBox_containsReal {c : ℚ} {panels : ℕ}
    (hc : 0 ≤ c) (hL : (11:ℚ)/16 ≤ c+(panels:ℚ)/32) (hU : c+(panels:ℚ)/32 ≤ 1)
    (hchecks : ∀ i < panels, psiPreciseGridChecks (c+(i:ℚ)/32)) :
    (psiOneCompactAnchorBox c panels).ContainsReal (psi 1 (c:ℝ)) := by
  have hL' : (11:ℝ)/16 ≤ (c:ℝ)+(panels:ℝ)/32 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast] using
      (Rat.cast_mono (α := ℝ) hL)
  have hU' : (c:ℝ)+(panels:ℝ)/32 ≤ 1 := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_one] using
      (Rat.cast_mono (α := ℝ) hU)
  have hseed : compactAnchorBox.ContainsReal (psi 1 ((c:ℝ)+(panels:ℝ)/32)) := by
    simpa only [QInterval.ContainsReal, compactAnchorBox, Rat.cast_div, Rat.cast_pow,
      Rat.cast_zero, Rat.cast_one, Rat.cast_ofNat] using psi_one_precise_compact_seed_bounds hL' hU'
  have hcasting (i : ℕ) :
      (c:ℝ)+((i:ℕ):ℝ)*((1/32:ℚ):ℝ) = ((c+(i:ℚ)/32:ℚ):ℝ) := by
    push_cast
    ring
  have hend : (c:ℝ)+(panels:ℝ)*((1/32:ℚ):ℝ) = (c:ℝ)+(panels:ℝ)/32 := by
    push_cast
    ring
  have h := psiOneUniformGridBox_containsReal compactAnchorBox (compactGridJet c) 36
    (a := (c:ℝ)) (h := (1:ℚ)/32) (by exact_mod_cast hc) (by norm_num) 0 panels
    (by rw [Nat.zero_add, hend]; linarith only [hU'])
    (by simpa only [Nat.zero_add, hend] using hseed) (by
      intro i hi j _
      have hi' : i < panels := by simpa only [Nat.zero_add] using (Finset.mem_Ico.mp hi).2
      have hpos : 0 ≤ c+(i:ℚ)/32 := by positivity
      have hle : (i:ℚ) ≤ panels := by exact_mod_cast hi'.le
      have hbound : c+(i:ℚ)/32 ≤ 2 := by linarith only [hle,hU]
      rw [hcasting]
      exact psiPreciseGridPhiJetBox_containsReal hpos hbound (hchecks i hi') j)
  simpa only [psiOneCompactAnchorBox, Nat.cast_zero, zero_mul, add_zero] using h

/-- Centers share the same 1/32-grid anchors. Only the short panel from
the center to its first anchor needs to be checked separately. -/
def psiOneCompactCornerFromAnchorBox (c : ℚ) (anchor : ℕ) (right : QInterval) : QInterval :=
  psiOnePanelBox right (psiPreciseGridPhiJetBox c) 36 ((anchor:ℚ)/32-c)

theorem psiOneCompactCornerFromAnchorBox_containsReal {c : ℚ} {anchor : ℕ} {right : QInterval}
    (hc : 0 ≤ c) (hca : c ≤ (anchor:ℚ)/32) (ha : anchor ≤ 22)
    (hcheck : psiPreciseGridChecks c)
    (hright : right.ContainsReal (psi 1 ((anchor:ℝ)/32))) :
    (psiOneCompactCornerFromAnchorBox c anchor right).ContainsReal (psi 1 (c:ℝ)) := by
  have haQ : (anchor:ℚ) ≤ 22 := by exact_mod_cast ha
  have haR : (anchor:ℝ) ≤ 22 := by exact_mod_cast ha
  have hh : (c:ℝ) + ((((anchor:ℚ)/32-c):ℚ):ℝ) = (anchor:ℝ)/32 := by
    push_cast
    ring
  unfold psiOneCompactCornerFromAnchorBox
  apply psiOnePanelBox_containsReal (by exact_mod_cast hc) (sub_nonneg.mpr hca)
  · rw [hh]
    linarith only [haR]
  · rwa [hh]
  · intro j _
    exact psiPreciseGridPhiJetBox_containsReal hc (by linarith only [hca, haQ]) hcheck j

#print axioms psiOneCompactAnchorBox_containsReal
#print axioms psiOneCompactCornerFromAnchorBox_containsReal

end Nuttall
