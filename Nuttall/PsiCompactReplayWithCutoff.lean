import Nuttall.PsiOneCompactGridReplay
import Nuttall.PsiOneCompactBlock40
import Nuttall.PsiTwoCompactBlock36
import Nuttall.PsiOneCompactBlock32
import Nuttall.PsiFirstCellSigns

import Nuttall.PsiOneCompactBlock24
import Nuttall.PsiTwoCompactBlock28

import Nuttall.PsiOneCompactBlock16
import Nuttall.PsiTwoCompactBlock20
import Nuttall.PsiTwoCompactCell0

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

/-- The rank-five through rank-seven minimum follows from cells below index 36. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_firstThirtySix {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ i : Fin 36, ∀ p ≤ 7, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 :=
  kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇
    (psi_compact_replay_with_cutoff (n := 36)
      psiOne_compact_from_cell36_signed_wronskians hcell)

/-- Only indices below 40 remain in the rank-eight compact assembly. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstForty
    (hcell : ∀ i : Fin 40, ∀ p ≤ 8, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 :=
  kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
    (psi_compact_replay_with_cutoff (n := 40)
      psiTwo_compact_from_cell40_signed_wronskians hcell)

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_firstThirtySix
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstForty

/-- The certified origin cell and right interval leave only cells 1 through 31. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_middleCells {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ i : Fin 32, 0 < i.val → ∀ p ≤ 7, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 := by
  apply kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇
  refine psi_compact_replay_with_cutoff (n := 32) psiOne_compact_from_cell32_signed_wronskians ?_
  intro i p hp t hleft hright
  by_cases hi : i.val = 0
  · apply psiOne_first_cell_signed_wronskians p hp t
    · simpa [hi] using hleft
    · simpa [hi] using hright
  · exact hcell i (Nat.pos_of_ne_zero hi) p hp t hleft hright

/-- Only indices below 36 remain in the rank-eight compact assembly. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstThirtySix
    (hcell : ∀ i : Fin 36, ∀ p ≤ 8, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 :=
  kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
    (psi_compact_replay_with_cutoff (n := 36)
      psiTwo_compact_from_cell36_signed_wronskians hcell)

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_middleCells
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstThirtySix

/-- The certified origin cell and right interval leave only cells 1 through 23. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_cellsOneThroughTwentyThree {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ i : Fin 24, 0 < i.val → ∀ p ≤ 7, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 := by
  apply kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇
  refine psi_compact_replay_with_cutoff (n := 24) psiOne_compact_from_cell24_signed_wronskians ?_
  intro i p hp t hleft hright
  by_cases hi : i.val = 0
  · apply psiOne_first_cell_signed_wronskians p hp t
    · simpa [hi] using hleft
    · simpa [hi] using hright
  · exact hcell i (Nat.pos_of_ne_zero hi) p hp t hleft hright

/-- Only indices below 28 remain in the rank-eight compact assembly. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstTwentyEight
    (hcell : ∀ i : Fin 28, ∀ p ≤ 8, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 :=
  kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
    (psi_compact_replay_with_cutoff (n := 28)
      psiTwo_compact_from_cell28_signed_wronskians hcell)

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_cellsOneThroughTwentyThree
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstTwentyEight

/-- Assemble a certified origin cell and right interval around the remaining cells. -/
theorem psi_compact_replay_with_origin {m r n : ℕ}
    (hzero : ∀ p ≤ r, ∀ t : ℝ, 0 ≤ t → t ≤ 1/128 →
      0 < kernelMinorSign p * wronskian (psi m) p t)
    (hright : ∀ p ≤ r, ∀ t : ℝ, (n:ℝ)/128 ≤ t →
      0 < kernelMinorSign p * wronskian (psi m) p t)
    (hcell : ∀ i : Fin n, 0 < i.val → ∀ p ≤ r, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi m) p t) :
    ∀ p ≤ r, ∀ t : ℝ, 0 ≤ t → t ≤ 53/128 →
      0 < kernelMinorSign p * wronskian (psi m) p t := by
  refine psi_compact_replay_with_cutoff hright ?_
  intro i p hp t hleft hright'
  by_cases hi : i.val = 0
  · exact hzero p hp t (by simpa [hi] using hleft) (by simpa [hi] using hright')
  · exact hcell i (Nat.pos_of_ne_zero hi) p hp t hleft hright'

/-- Only cells 1 through 15 remain for the first integration through order seven. -/
theorem kernelIntegrationOrder_eq_one_of_psiOne_firstSixteenWithOrigin {r : ℕ}
    (hr₅ : 5 ≤ r) (hr₇ : r ≤ 7)
    (hcell : ∀ i : Fin 16, 0 < i.val → ∀ p ≤ 7, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 1) p t) :
    kernelIntegrationOrder r = 1 :=
  kernelIntegrationOrder_eq_one_of_psiOne_compact hr₅ hr₇
    (psi_compact_replay_with_origin psiOne_first_cell_signed_wronskians
      psiOne_compact_from_cell16_signed_wronskians hcell)

/-- Only cells 1 through 19 remain for the second integration through order eight. -/
theorem kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstTwentyWithOrigin
    (hcell : ∀ i : Fin 20, 0 < i.val → ∀ p ≤ 8, ∀ t : ℝ, (i.val:ℝ)/128 ≤ t →
      t ≤ ((i.val+1:ℕ):ℝ)/128 →
      0 < kernelMinorSign p * wronskian (psi 2) p t) :
    kernelIntegrationOrder 8 = 2 := by
  apply kernelIntegrationOrder_eight_eq_two_of_psiTwo_compact
  refine psi_compact_replay_with_origin ?_ psiTwo_compact_from_cell20_signed_wronskians hcell
  intro p hp t hleft hright
  exact psiTwo_compact_cell0_signed_wronskians p hp t (by simpa using hleft) hright

#print axioms kernelIntegrationOrder_eq_one_of_psiOne_firstSixteenWithOrigin
#print axioms kernelIntegrationOrder_eight_eq_two_of_psiTwo_firstTwentyWithOrigin

end Nuttall
