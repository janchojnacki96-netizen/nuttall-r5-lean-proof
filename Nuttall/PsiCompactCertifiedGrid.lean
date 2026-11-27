import Nuttall.PsiCompactGridIndex
import Nuttall.PsiCompactFixedJetCell
import Nuttall.PsiCompactSharedAnchors

namespace Nuttall

open W5

/-- Assemble a complete compact certificate from the shared panels, center jets,
short-panel enclosures, and integer matrix row checks. -/
theorem psiOne_compact_certified_grid_signed_wronskians
    (panels : ℕ → QInterval) (gridJets : ℕ → ℕ → QInterval)
    (hgrid : ∀ i < 22, ∀ j < 36,
      (gridJets i j).ContainsReal (iteratedDeriv j Phi ((i:ℝ)/32)))
    (hpanels : ∀ i < 22,
      let panel := psiOnePanelBox (QInterval.point 0) (gridJets i) 36 (1/32)
      (panels i).lo ≤ panel.lo ∧ panel.hi ≤ (panels i).hi)
    (anchor : Fin 67 → Fin 23) (corners : Fin 67 → QInterval)
    (centerJets : Fin 67 → ℕ → QInterval)
    (hanchor : ∀ i, psiOneCellCenter (psiOneCompactCell i) ≤ ((anchor i).val:ℚ)/32)
    (hjets : ∀ i, ∀ j < 36, (centerJets i j).ContainsReal
      (iteratedDeriv j Phi (psiOneCellCenter (psiOneCompactCell i):ℝ)))
    (hshort : ∀ i,
      let n := (anchor i).val
      let center := psiOneCellCenter (psiOneCompactCell i)
      let raw := psiOnePanelBox (psiOneCompactAnchorFromPanels panels n (22-n))
        (centerJets i) 36 ((n:ℚ)/32-center)
      (corners i).lo ≤ raw.lo ∧ raw.hi ≤ (corners i).hi)
    (hrows : ∀ i j, psiOneCompactFixedRow i
      (psiOneCompactBoxesOfJets (psiOneCellRadius (psiOneCompactCell i))
        (corners i) (centerJets i)) j < psiOneCompactFixedThreshold)
    (p : ℕ) (hp : p ≤ 7) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_indexed_grid_signed_wronskians ?_ p hp t ht₀ ht₁
  intro i rank hrank v hv
  let n := (anchor i).val
  let center := psiOneCellCenter (psiOneCompactCell i)
  let radius := psiOneCellRadius (psiOneCompactCell i)
  obtain ⟨hleft, hright, hrad, hwidth⟩ := psiOneCompactCell_geometry i
  change 0 ≤ (center:ℝ)-(radius:ℝ) at hleft
  change 0 ≤ (radius:ℝ) at hrad
  have hn : n ≤ 22 := Nat.le_of_lt_succ (anchor i).isLt
  have hc : 0 ≤ center := by
    have hcenter : 0 ≤ (center:ℝ) := by linarith only [hleft, hrad]
    exact_mod_cast hcenter
  have hanchorValue := psiOneCompactAnchorFromPanels_containsReal panels gridJets hgrid
    hpanels n (22-n) (Nat.add_sub_of_le hn)
  have hq := psiOneCompactShortPanel_containsReal hc (hanchor i) hn hanchorValue (hjets i)
  have hcorner : (corners i).ContainsReal (psi 1 (center:ℝ)) :=
    compactContainsReal_of_endpoints (hshort i).1 (hshort i).2 hq
  exact psiOne_compact_fixed_jet_cell_signed_wronskians hrank center radius
    hleft hright hrad hwidth hv i hcorner (hjets i) (hrows i)

#print axioms psiOne_compact_certified_grid_signed_wronskians

end Nuttall
