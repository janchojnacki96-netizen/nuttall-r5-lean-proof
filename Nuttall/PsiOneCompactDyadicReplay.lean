import Nuttall.PsiOneCompactDyadicCell
import Nuttall.PsiFixedGridJets
import Nuttall.PsiCompactSharedAnchors

namespace Nuttall

open W5

/-- Center of a uniform cell before the analytic cutoff. -/
def psiOneDyadicCenter (i : Fin 53) : ℚ := (2*(i.val:ℚ)+1)/256

/-- Data for one short quadrature panel and its rank-seven certificate. -/
structure PsiOneDyadicSnapshot where
  input : PsiPreciseGridInputs
  jets : ℕ → FixedIntInterval
  corner : FixedIntInterval

/-- The final output depends only on the verified shared anchor and the finite checks. -/
theorem psiOne_compact_dyadic_snapshot_sound (i : Fin 53) (anchor : ℕ)
    (hₐ : anchor ≤ 22) (hcₐ : psiOneDyadicCenter i ≤ (anchor:ℚ)/32)
    (right : QInterval) (hright : right.ContainsReal (psi 1 ((anchor:ℝ)/32)))
    (s : PsiOneDyadicSnapshot)
    (hinput : psiPreciseGridChecks (psiOneDyadicCenter i) ∧
      psiPreciseGridInputs (psiOneDyadicCenter i) = s.input)
    (hjet : ∀ j < 36, (s.jets j).asQInterval (2^90) = psiFixedGridPhiJetBoxOfInputs s.input j)
    (hcorner :
      let raw := psiOnePanelBox right (fun j => (s.jets j).asQInterval (2^90)) 36
        ((anchor:ℚ)/32 - psiOneDyadicCenter i)
      (s.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
        raw.hi ≤ (s.corner.asQInterval (2^90)).hi)
    (hmargin : ∀ j, psiOneCompactDyadicRow (i.castLE (by decide)) s.corner s.jets j <
      psiOneCompactDyadicThreshold)
    (p : ℕ) (hp : p ≤ 7) (t : ℝ)
    (hleft : (i.val:ℝ)/128 ≤ t) (hright' : t ≤ ((i.val+1:ℕ):ℝ)/128) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  have hi : (i.val:ℝ) < 53 := by exact_mod_cast i.isLt
  have hi₀ : (0:ℝ) ≤ (i.val:ℝ) := by positivity
  have hc₀ : 0 ≤ psiOneDyadicCenter i := by unfold psiOneDyadicCenter; positivity
  have hcR : (psiOneDyadicCenter i:ℝ) = (2*(i.val:ℝ)+1)/256 := by
    unfold psiOneDyadicCenter
    push_cast <;> rfl
  have hc₂ : psiOneDyadicCenter i ≤ 2 := by
    have h : (psiOneDyadicCenter i:ℝ) ≤ 2 := by rw [hcR]; linarith only [hi]
    exact_mod_cast h
  have hjets (j : ℕ) (hj : j < 36) :
      ((s.jets j).asQInterval (2^90)).ContainsReal (iteratedDeriv j Phi (psiOneDyadicCenter i:ℝ)) := by
    rw [hjet j hj]
    exact psiFixedGridPhiJetBoxOfInputs_containsReal hc₀ hc₂ hinput.1 hinput.2 j
  have hQ := psiOneCompactShortPanel_containsReal hc₀ hcₐ hₐ hright hjets
  have hC := compactContainsReal_of_endpoints hcorner.1 hcorner.2 hQ
  let v := 256*t-(2*(i.val:ℝ)+1)
  have hr : t ≤ ((i.val:ℝ)+1)/128 := by exact_mod_cast hright'
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hleft],
    by dsimp [v]; linarith only [hr]⟩
  have ht : (psiOneDyadicCenter i:ℝ)+(1/256)*v = t := by rw [hcR]; dsimp [v]; ring
  have h := psiOne_compact_dyadic_cell_signed_wronskians hp
    (c := (psiOneDyadicCenter i:ℝ)) (by rw [hcR]; linarith only [hi₀])
    (by rw [hcR]; linarith only [hi]) hv (i.castLE (by decide)) hC hjets hmargin
  rwa [ht] at h

#print axioms psiOne_compact_dyadic_snapshot_sound

end Nuttall
