import Nuttall.PsiOneCompactDyadicReplay
import Nuttall.PsiTwoCompactCellSigns
import Nuttall.PsiTwoPanelBox

namespace Nuttall

open W5
open scoped BigOperators

/-- At a cell center, both integrated kernels use the same analytic theta jets. -/
theorem psiTwo_compact_dyadic_snapshot_sound (i : Fin 53) (anchor : ℕ)
    (hₐ : anchor ≤ 22) (hcₐ : psiOneDyadicCenter i ≤ (anchor:ℚ)/32)
    (rightOne rightTwo : QInterval)
    (hOne : rightOne.ContainsReal (psi 1 ((anchor:ℝ)/32)))
    (hTwo : rightTwo.ContainsReal (psi 2 ((anchor:ℝ)/32)))
    (s : PsiOneDyadicSnapshot) (two : FixedIntInterval)
    (hinput : psiPreciseGridChecks (psiOneDyadicCenter i) ∧
      psiPreciseGridInputs (psiOneDyadicCenter i) = s.input)
    (hjet : ∀ j < 36, (s.jets j).asQInterval (2^90) = psiFixedGridPhiJetBoxOfInputs s.input j)
    (hcorner :
      let raw := psiOnePanelBox rightOne (fun j => (s.jets j).asQInterval (2^90)) 36
        ((anchor:ℚ)/32 - psiOneDyadicCenter i)
      (s.corner.asQInterval (2^90)).lo ≤ raw.lo ∧
        raw.hi ≤ (s.corner.asQInterval (2^90)).hi)
    (hcornerTwo :
      let raw := psiTwoPanelBox rightOne rightTwo (fun j => (s.jets j).asQInterval (2^90))
        ((anchor:ℚ)/32 - psiOneDyadicCenter i)
      (two.asQInterval (2^90)).lo ≤ raw.lo ∧ raw.hi ≤ (two.asQInterval (2^90)).hi)
    (B : Matrix (Fin 8) (Fin 8) ℤ) (hlower : B.IsLowerTriangular)
    (hdiag : ∀ j, B j j ≠ 0) (hrow : ∀ j, (∑ k, |B j k|) ≤ 1024*6700000)
    (hmargin : ∀ j, psiTwoCompactRow B s.corner two s.jets j < psiTwoCompactThreshold)
    (p : ℕ) (hp : p ≤ 8) (t : ℝ)
    (hleft : (i.val:ℝ)/128 ≤ t) (hright : t ≤ ((i.val+1:ℕ):ℝ)/128) :
    0 < kernelMinorSign p * wronskian (psi 2) p t := by
  let c : ℚ := psiOneDyadicCenter i
  let h : ℚ := (anchor:ℚ)/32-c
  have hi : (i.val:ℝ) < 53 := by exact_mod_cast i.isLt
  have hi₀ : (0:ℝ) ≤ (i.val:ℝ) := by positivity
  have hcR : (c:ℝ) = (2*(i.val:ℝ)+1)/256 := by
    unfold c psiOneDyadicCenter
    push_cast <;> rfl
  have hc₀ : 0 ≤ c := by unfold c psiOneDyadicCenter; positivity
  have hc₂ : c ≤ 2 := by
    have hu : (c:ℝ) ≤ 2 := by rw [hcR]; linarith only [hi]
    exact_mod_cast hu
  have hjets (j : ℕ) (hj : j < 36) :
      ((s.jets j).asQInterval (2^90)).ContainsReal (iteratedDeriv j Phi (c:ℝ)) := by
    rw [show c = psiOneDyadicCenter i by rfl, hjet j hj]
    exact psiFixedGridPhiJetBoxOfInputs_containsReal hc₀ hc₂ hinput.1 hinput.2 j
  have he : (c:ℝ)+(h:ℝ) = (anchor:ℝ)/32 := by unfold h; push_cast; ring
  have har : (anchor:ℝ) ≤ 22 := by exact_mod_cast hₐ
  have hQ := psiOneCompactShortPanel_containsReal hc₀ hcₐ hₐ hOne hjets
  have hC := compactContainsReal_of_endpoints hcorner.1 hcorner.2 hQ
  have hQ₂ := psiTwoPanelBox_containsReal (a := (c:ℝ)) (h := h)
    (by exact_mod_cast hc₀) (sub_nonneg.mpr hcₐ)
    (by rw [he]; linarith only [har]) (by rwa [he]) (by rwa [he]) hjets
  have hC₂ := compactContainsReal_of_endpoints hcornerTwo.1 hcornerTwo.2 hQ₂
  let v := 256*t-(2*(i.val:ℝ)+1)
  have hr : t ≤ ((i.val:ℝ)+1)/128 := by exact_mod_cast hright
  have hv : |v| ≤ 1 := abs_le.mpr ⟨by dsimp [v]; linarith only [hleft],
    by dsimp [v]; linarith only [hr]⟩
  have ht : (c:ℝ)+(1/256)*v = t := by rw [hcR]; dsimp [v]; ring
  rw [← ht]
  exact psiTwo_compact_fixed_cell_signed_wronskians hp
    (by rw [hcR]; linarith only [hi₀]) (by rw [hcR]; linarith only [hi]) hv
    B hlower hdiag hrow s.corner two s.jets hC hC₂ hjets hmargin

#print axioms psiTwo_compact_dyadic_snapshot_sound

end Nuttall
