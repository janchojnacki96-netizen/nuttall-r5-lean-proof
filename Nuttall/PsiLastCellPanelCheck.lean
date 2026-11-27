import Nuttall.PsiLastCellGridInputs
import Nuttall.PsiCompactPrecisionSeed
import Nuttall.PsiLastCellJetData

namespace Nuttall

open W5

private def lastCellPanelWidth (i : Fin 7) : ℚ :=
  if i = 0 then 1/512 else 1/32

private def lastCellPanelRaw (i : Fin 7) : QInterval :=
  psiOnePanelBox (QInterval.point 0) (psiPreciseGridPhiJetBoxOfInputs (psiLastCellGridInputs i))
    36 (lastCellPanelWidth i)

private def lastCellPanelCheck (i : Fin 7) : Prop :=
  (psiLastCellPanelSnapshot i).lo ≤ (lastCellPanelRaw i).lo ∧
    (lastCellPanelRaw i).hi ≤ (psiLastCellPanelSnapshot i).hi

private instance (i : Fin 7) : Decidable (lastCellPanelCheck i) := by
  unfold lastCellPanelCheck
  infer_instance

set_option maxRecDepth 65536 in
set_option maxHeartbeats 45000000 in
private theorem lastCellPanel_checked (i : Fin 7) : lastCellPanelCheck i := by
  fin_cases i <;> decide +kernel

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
  have hjets (j : ℕ) :
      (psiPreciseGridPhiJetBoxOfInputs (psiLastCellGridInputs i) j).ContainsReal
        (iteratedDeriv j Phi (psiLastCellNode i:ℝ)) := by
    have hj := psiPreciseGridPhiJetBox_containsReal hc hc₂ hg.1 j
    rwa [psiPreciseGridPhiJetBox, hg.2] at hj
  have h := psiOnePanelBox_containsReal (d := 36) (by exact_mod_cast hc) hh hb' hright
    (fun j _ => hjets j)
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

private def lastCellSeed : QInterval := ⟨0, 1/10^16⟩

theorem psiOneLastCellCornerSnapshot_containsReal :
    psiOneLastCellCornerSnapshot.ContainsReal (psi 1 (255/512)) := by
  have hlast : (psiLastCellNode 6:ℝ)+(lastCellPanelWidth 6:ℝ) = 11/16 := by
    have h : psiLastCellNode 6 + lastCellPanelWidth 6 = 11/16 := by decide +kernel
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) h
  have hseed : lastCellSeed.ContainsReal (psi 1 (11/16)) := by
    have h := psi_one_precise_compact_seed_bounds (t := 11/16) (by norm_num) (by norm_num)
    simpa only [lastCellSeed, QInterval.ContainsReal, Rat.cast_zero, Rat.cast_div,
      Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using h
  have h₆ := lastCellPanel_containsReal 6 (right := lastCellSeed) (by rwa [hlast])
  have h₅ := lastCellPanel_containsReal 5 (by rw [lastCellNode_next (5:Fin 6)]; exact h₆)
  have h₄ := lastCellPanel_containsReal 4 (by rw [lastCellNode_next (4:Fin 6)]; exact h₅)
  have h₃ := lastCellPanel_containsReal 3 (by rw [lastCellNode_next (3:Fin 6)]; exact h₄)
  have h₂ := lastCellPanel_containsReal 2 (by rw [lastCellNode_next (2:Fin 6)]; exact h₃)
  have h₁ := lastCellPanel_containsReal 1 (by rw [lastCellNode_next (1:Fin 6)]; exact h₂)
  have h₀ := lastCellPanel_containsReal 0 (by rw [lastCellNode_next (0:Fin 6)]; exact h₁)
  have ht : (psiLastCellNode 0:ℝ) = 255/512 := by
    have h : psiLastCellNode 0 = 255/512 := by decide +kernel
    simpa only [Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ => (q:ℝ)) h
  rw [ht] at h₀
  exact compactContainsReal_of_endpoints (by decide +kernel) (by decide +kernel) h₀

#print axioms psiOneLastCellCornerSnapshot_containsReal

end Nuttall
