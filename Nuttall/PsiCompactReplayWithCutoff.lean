import Nuttall.PsiOneCompactGridReplay
import Nuttall.PsiOneCompactBlock40
import Nuttall.PsiTwoCompactCell47

namespace Nuttall

/-- Assemble the remaining cells strictly to the left of an already certified right interval. -/
theorem psi_compact_replay_with_cutoff {m r n : ℕ}
    (hright : ∀ p ≤ r, ∀ t : ℝ, (n:ℝ)/128 ≤ t →
      0 < kernelMinorSign p * wronskian (psi m) p t)
    (hcell : ∀ i : Fin n, ∀ p ≤ r, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi m) p t) :
    ∀ p ≤ r, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi m) p t := by
  intro p hp t ht₀ ht₁
  obtain ⟨ab, hab, ha, hb⟩ := psiOneCompactPrefix_cover ht₀ ht₁
  obtain ⟨i, rfl⟩ := psiOneCompactPrefix_cell_index hab
  have ha' : (i.val:ℝ)/128 ≤ t := by
    simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using ha
  by_cases h : i.val < n
  · exact hcell ⟨i.val, h⟩ p hp t ha'
      (by simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hb)
  · have hn : (n:ℝ) ≤ i.val := by exact_mod_cast le_of_not_gt h
    exact hright p hp t ((div_le_div_of_nonneg_right hn (by norm_num)).trans ha')

/-- Only indices below 40 remain in the Ψ₁ compact assembly. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_firstForty {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ i : Fin 40, ∀ p ≤ 7, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 := by
  apply kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇
  refine psi_compact_replay_with_cutoff (n := 40) ?_ hcell
  intro p hp t ht
  exact psiOne_compact_from_fiveSixteen_signed_wronskians p hp t (by linarith only [ht])

/-- Only indices below 47 remain in the Ψ₂ compact assembly. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstFortySeven
    (hcell : ∀ i : Fin 47, ∀ p ≤ 8, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 :=
  kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
    (psi_compact_replay_with_cutoff (n := 47) psiTwo_compact_from_fortySeven128_signed_wronskians
      hcell)

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_firstForty
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstFortySeven

end Nuttall
