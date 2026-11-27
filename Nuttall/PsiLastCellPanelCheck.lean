import Nuttall.PsiLastCellPanelReplay
import Nuttall.PsiCompactPrecisionSeed
import Nuttall.PsiLastCellJetData

namespace Nuttall

open W5

private theorem lastCellPanel_containsReal (i : Fin 7) {right : QInterval}
    (hright : right.ContainsReal (psi 1 ((psiLastCellNode i:ℝ)+(lastCellPanelWidth i:ℝ)))) :
    (QInterval.add right (psiLastCellPanelSnapshot i)).ContainsReal (psi 1 (psiLastCellNode i:ℝ)) := by
  have hc : (0:ℚ) ≤ psiLastCellNode i := by fin_cases i <;> decide +kernel
  have hh : (0:ℚ) ≤ lastCellPanelWidth i := by fin_cases i <;> decide +kernel
  have hb : psiLastCellNode i + lastCellPanelWidth i ≤ 2 := by
    fin_cases i <;> decide +kernel
  have hb' : (psiLastCellNode i:ℝ)+(lastCellPanelWidth i:ℝ) ≤ 2 := by
    simpa only [Rat.cast_add, Rat.cast_ofNat] using (Rat.cast_mono (K := ℝ) hb)
  have hc₂ : psiLastCellNode i ≤ 2 := by linarith only [hh, hb]
  have hg := psiLastCellGridInputs_checked i
  have hjets (j : ℕ) (hj : j ∈ Finset.range 36) :
      (lastCellPanelJet i j).ContainsReal
        (iteratedDeriv j Phi (psiLastCellNode i:ℝ)) := by
    rw [lastCellPanelJet_checked i j (Finset.mem_range.mp hj)]
    exact psiFixedGridPhiJetBoxOfInputs_containsReal hc hc₂ hg.1 hg.2 j
  have h := psiOnePanelBox_containsReal (by exact_mod_cast hc) hh hb' hright hjets
  rw [psiOnePanelBox_eq_add_zero] at h
  have hm := lastCellPanel_checked i
  exact compactContainsReal_of_endpoints (add_le_add (le_refl right.lo) hm.1)
    (add_le_add (le_refl right.hi) hm.2) h

private theorem lastCellNode_next (i : Fin 6) :
    (psiLastCellNode (i.castLE (by decide)):ℝ) +
        (lastCellPanelWidth (i.castLE (by decide)):ℝ) = (psiLastCellNode i.succ:ℝ) := by
  have h := (show psiLastCellNode (i.castLE (by decide)) +
      lastCellPanelWidth (i.castLE (by decide)) = psiLastCellNode i.succ from
    by fin_cases i <;> decide +kernel)
  simpa only [Rat.cast_add] using congrArg (fun q : ℚ => (q:ℝ)) h

private theorem lastCellPanelStep (i : Fin 6) {right : QInterval}
    (hright : right.ContainsReal (psi 1 (psiLastCellNode i.succ:ℝ))) :
    (right.add (psiLastCellPanelSnapshot (i.castLE (by decide)))).ContainsReal
      (psi 1 (psiLastCellNode (i.castLE (by decide)):ℝ)) :=
  lastCellPanel_containsReal (i.castLE (by decide)) (by rwa [lastCellNode_next i])

private def lastCellSeed : QInterval := ⟨0, 1/10^16⟩

/-- Anchor at 1/2 shared by the last compact cells. -/
def psiOneCompactHalfAnchor : QInterval :=
  ([6, 5, 4, 3, 2, 1] : List (Fin 7)).foldl
    (fun right i => right.add (psiLastCellPanelSnapshot i)) lastCellSeed

theorem psiOneCompactHalfAnchor_containsReal :
    psiOneCompactHalfAnchor.ContainsReal (psi 1 (1/2)) := by
  have hlast : (psiLastCellNode 6:ℝ)+(lastCellPanelWidth 6:ℝ) = 11/16 := by
    have h : psiLastCellNode 6 + lastCellPanelWidth 6 = 11/16 := by decide +kernel
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) h
  have hseed : lastCellSeed.ContainsReal (psi 1 (11/16)) := by
    have h := psi_one_precise_compact_seed_bounds (t := 11/16) (by norm_num) (by norm_num)
    simpa only [lastCellSeed, QInterval.ContainsReal, Rat.cast_zero, Rat.cast_div,
      Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using h
  have h₆ := lastCellPanel_containsReal 6 (right := lastCellSeed) (by rwa [hlast])
  have h₅ := lastCellPanelStep 5 h₆
  have h₄ := lastCellPanelStep 4 h₅
  have h₃ := lastCellPanelStep 3 h₄
  have h₂ := lastCellPanelStep 2 h₃
  have h₁ := lastCellPanelStep 1 h₂
  have ht : (psiLastCellNode 1:ℝ) = 1/2 := by
    have h : psiLastCellNode 1 = 1/2 := by decide +kernel
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) h
  rwa [ht] at h₁

theorem psiOneLastCellCornerSnapshot_containsReal :
    psiOneLastCellCornerSnapshot.ContainsReal (psi 1 (255/512)) := by
  have hnext : (psiLastCellNode 0:ℝ)+(lastCellPanelWidth 0:ℝ) = 1/2 := by
    have h : psiLastCellNode 0 + lastCellPanelWidth 0 = 1/2 := by decide +kernel
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
      congrArg (fun q : ℚ => (q:ℝ)) h
  have h₀ := lastCellPanel_containsReal 0 (by rw [hnext]; exact psiOneCompactHalfAnchor_containsReal)
  have ht : (psiLastCellNode 0:ℝ) = 255/512 := by
    have h : psiLastCellNode 0 = 255/512 := by decide +kernel
    simpa only [Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) h
  rw [ht] at h₀
  exact compactContainsReal_of_endpoints (by decide +kernel) (by decide +kernel) h₀

#print axioms psiOneLastCellCornerSnapshot_containsReal
#print axioms psiOneCompactHalfAnchor_containsReal

end Nuttall
