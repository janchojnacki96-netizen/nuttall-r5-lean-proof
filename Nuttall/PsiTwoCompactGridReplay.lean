import Nuttall.PsiOneCompactGridReplay
import Nuttall.PsiTwoCompactCell52
import Nuttall.PhiRankEightTailSigns

namespace Nuttall

/-- Join the first certified rank-eight cell to the analytic tail. -/
theorem psiTwo_compact_right_block_signed_wronskians (p : ℕ) (hp : p ≤ 8)
    (t : ℝ) (ht : 13/32 ≤ t) : 0 < kernelMinorSign p * wronskian (psi 2) p t := by
  by_cases h : t ≤ 53/128
  · exact psiTwo_compact_cell52_signed_wronskians p hp t ht h
  exact psi_signed_wronskian_pos_on_compact_tail 2 hp (le_of_not_ge h)

/-- Given the compact checks, the upper bound and the existing obstruction give m(8)=2. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_prefix_replay
    (hcell : ∀ i : Fin 52, ∀ p ≤ 8, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 := by
  apply kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
  intro p hp t ht₀ ht₁
  obtain ⟨ab, hab, ha, hb⟩ := psiOneCompactPrefix_cover ht₀ ht₁
  obtain ⟨i, rfl⟩ := psiOneCompactPrefix_cell_index hab
  by_cases h : i.val < 52
  · exact hcell ⟨i.val, h⟩ p hp t
      (by simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using ha)
      (by simpa only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] using hb)
  · have he : i.val = 52 := by have := i.isLt; omega
    simp only [he, Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at ha
    exact psiTwo_compact_right_block_signed_wronskians p hp t (by linarith only [ha])

#print axioms psiTwo_compact_right_block_signed_wronskians
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_prefix_replay

end Nuttall
