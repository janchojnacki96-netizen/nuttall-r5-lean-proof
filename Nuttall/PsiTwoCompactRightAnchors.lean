import Nuttall.PsiCompactUniformPanel14
import Nuttall.PsiTwoPanelAnchors

namespace Nuttall

open W5

private def rightPanels (i : ℕ) : QInterval :=
  if i = 14 then psiOneUniformPanel14
  else if i = 15 then psiOneUniformPanel15
  else psiLastCellPanelSnapshot ⟨(i-15)%7, Nat.mod_lt _ (by decide)⟩

private def rightJets (i : ℕ) : ℕ → QInterval :=
  if i = 14 then psiOneUniformPanel14Jet
  else if i = 15 then psiOneUniformPanel15Jet
  else lastCellPanelJet ⟨(i-15)%7, Nat.mod_lt _ (by decide)⟩

private theorem lastPanelNode_data (i : Fin 6) :
    psiLastCellNode i.succ = ((i.val+16:ℕ):ℚ)/32 ∧ lastCellPanelWidth i.succ = 1/32 := by
  fin_cases i <;> decide +kernel

private theorem rightJet_valid (i j : ℕ) (hi : 14 ≤ i) (hi₂ : i < 22) (hj : j < 36) :
    (rightJets i j).ContainsReal (iteratedDeriv j Phi ((i:ℝ)/32)) := by
  obtain rfl | h₁ := eq_or_lt_of_le hi
  · simpa [rightJets] using psiOneUniformPanel14Jet_containsReal j hj
  obtain rfl | h₂ := eq_or_lt_of_le (show 15 ≤ i by omega)
  · simpa [rightJets] using psiOneUniformPanel15Jet_containsReal j hj
  let k : Fin 6 := ⟨i-16, by omega⟩
  have hk : (k.val+16:ℕ) = i := by dsimp [k]; omega
  have he : ⟨(i-15)%7, Nat.mod_lt _ (by decide)⟩ = k.succ := by
    apply Fin.ext
    dsimp [k]
    rw [Nat.mod_eq_of_lt (by omega : i-15 < 7)]
    omega
  have hn : psiLastCellNode k.succ = (i:ℚ)/32 := by rw [(lastPanelNode_data k).1, hk]
  have hg := psiLastCellGridInputs_checked k.succ
  have hc : 0 ≤ psiLastCellNode k.succ := by rw [hn]; positivity
  have hc₂ : psiLastCellNode k.succ ≤ 2 := by
    rw [hn]
    have hiq : (i:ℚ) ≤ 22 := by exact_mod_cast hi₂.le
    linarith only [hiq]
  have hd := psiFixedGridPhiJetBoxOfInputs_containsReal hc hc₂ hg.1 hg.2 j
  rw [← lastCellPanelJet_checked k.succ j hj, hn] at hd
  simpa [rightJets, show i ≠ 14 by omega, show i ≠ 15 by omega, he] using hd

private theorem rightPanel_valid (i : ℕ) (hi : 14 ≤ i) (hi₂ : i < 22) :
    let panel := psiOnePanelBox (QInterval.point 0) (rightJets i) 36 (1/32)
    (rightPanels i).lo ≤ panel.lo ∧ panel.hi ≤ (rightPanels i).hi := by
  obtain rfl | h₁ := eq_or_lt_of_le hi
  · simpa [rightPanels, rightJets] using psiOneUniformPanel14_checked
  obtain rfl | h₂ := eq_or_lt_of_le (show 15 ≤ i by omega)
  · simpa [rightPanels, rightJets] using psiOneUniformPanel15_checked
  let k : Fin 6 := ⟨i-16, by omega⟩
  have he : ⟨(i-15)%7, Nat.mod_lt _ (by decide)⟩ = k.succ := by
    apply Fin.ext
    dsimp [k]
    rw [Nat.mod_eq_of_lt (by omega : i-15 < 7)]
    omega
  simpa [rightPanels, rightJets, show i ≠ 14 by omega, show i ≠ 15 by omega,
    he, LastCellPanelCheck, (lastPanelNode_data k).2] using lastCellPanel_checked k.succ

private theorem rightAnchors_valid (i n : ℕ) (hi : 14 ≤ i) (hend : i+n = 22) :
    (psiOneCompactAnchorFromPanels rightPanels i n).ContainsReal (psi 1 ((i:ℝ)/32)) ∧
    (psiTwoCompactAnchorFromPanels rightPanels rightJets i n).ContainsReal (psi 2 ((i:ℝ)/32)) := by
  induction n generalizing i with
  | zero =>
    have hi : i = 22 := by omega
    subst i
    exact ⟨by
      simpa [psiOneCompactAnchorFromPanels, QInterval.ContainsReal] using
        (psi_one_precise_compact_seed_bounds (t := 11/16) (by norm_num) (by norm_num)),
      by simpa only [psiTwoCompactAnchorFromPanels, show ((22:ℕ):ℝ)/32 = 11/16 by norm_num]
        using psiTwoPanelSeed_containsReal⟩
  | succ n ih =>
    have hi₂ : i < 22 := by omega
    have hir : (i:ℝ) ≤ 22 := by exact_mod_cast hi₂.le
    have hnext : ((i+1:ℕ):ℝ)/32 = (i:ℝ)/32+((1/32:ℚ):ℝ) := by push_cast; ring
    obtain ⟨hone, htwo⟩ := ih (i+1) (by omega) (by omega)
    rw [hnext] at hone htwo
    have hb : (i:ℝ)/32+((1/32:ℚ):ℝ) ≤ 2 := by push_cast; linarith only [hir]
    have hj (j : ℕ) (hj : j < 36) := rightJet_valid i j hi hi₂ hj
    constructor
    · have h := psiOnePanelBox_containsReal (by positivity) (by norm_num) hb hone
        (fun j hj' => hj j (Finset.mem_range.mp hj'))
      rw [psiOnePanelBox_eq_add_zero] at h
      have hbounds := rightPanel_valid i hi hi₂
      exact compactContainsReal_of_endpoints (add_le_add (le_refl _) hbounds.1)
        (add_le_add (le_refl _) hbounds.2) h
    · exact psiTwoPanelBox_containsReal (by positivity) (by norm_num) hb hone htwo hj

/-- Rank-eight Ψ₂ enclosure at the first shared anchor above the compact endpoint. -/
def psiTwoCompactAnchor14 : QInterval :=
  psiTwoCompactAnchorFromPanels rightPanels rightJets 14 8

theorem psiTwoCompactAnchor14_containsReal :
    psiTwoCompactAnchor14.ContainsReal (psi 2 ((14/32:ℚ):ℝ)) := by
  have h := (rightAnchors_valid 14 8 (by decide) (by decide)).2
  simpa [psiTwoCompactAnchor14] using h

#print axioms psiTwoCompactAnchor14_containsReal

end Nuttall
