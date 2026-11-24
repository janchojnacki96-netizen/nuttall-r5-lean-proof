import W5.ThetaLastCellReplayGamma0
import W5.ThetaLastCellReplayGamma1
import W5.ThetaLastCellReplayGamma2
import W5.ThetaLastCellGammaWExpChecked
import W5.ThetaLastCellGammaMomentSums
import W5.ThetaLastCellCompactDyadicGammaA
import W5.ThetaLastCellCompactDyadicGammaB

namespace W5

/-- Enlarging a rational enclosure preserves genuine real containment. -/
theorem thetaLastCellReplayWiden {A B : QInterval} {x : ℝ}
    (hlo : A.lo ≤ B.lo) (hhi : B.hi ≤ A.hi)
    (h : QInterval.ContainsReal B x) : QInterval.ContainsReal A x := by
  have hloR : (A.lo:ℝ) ≤ (B.lo:ℝ) := by exact_mod_cast hlo
  have hhiR : (B.hi:ℝ) ≤ (A.hi:ℝ) := by exact_mod_cast hhi
  exact ⟨hloR.trans h.1, h.2.trans hhiR⟩

theorem thetaLastCellGammaAllBins_checked (i : Fin 12) :
    ThetaLastCellGammaBinFits i := by
  fin_cases i
  · exact thetaLastCellGammaBin0_checked
  · exact thetaLastCellGammaBin1_checked
  · exact thetaLastCellGammaBin2_checked
  · exact thetaLastCellGammaBin3_checked
  · exact thetaLastCellGammaBin4_checked
  · exact thetaLastCellGammaBin5_checked
  · exact thetaLastCellGammaBin6_checked
  · exact thetaLastCellGammaBin7_checked
  · exact thetaLastCellGammaBin8_checked
  · exact thetaLastCellGammaBin9_checked
  · exact thetaLastCellGammaBin10_checked
  · exact thetaLastCellGammaBin11_checked

/-- The memoized bin calculator is exactly the old proved bin formula
when the endpoint exponential table has passed its equality check. -/
theorem thetaLastCellBinLower_bound (i : Fin 12) (k : Fin 9) :
    thetaLastCellBinLower i k ≤
      (thetaGammaLowerNineBin 8 (thetaLastCellA^2)
        (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).lo := by
  have h : thetaLastCellBinLower i k ≤
      (thetaGammaMemoLowerNineBin thetaLastCellWExp 8 (thetaLastCellA^2)
        (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).lo :=
    (thetaLastCellGammaAllBins_checked i k).1
  rw [thetaGammaMemoLowerNineBin_eq thetaLastCellWExp thetaLastCellWExp_eq] at h
  exact h

theorem thetaLastCellBinUpper_bound (i : Fin 12) (k : Fin 9) :
    (thetaGammaUpperNineBin 8 (thetaLastCellB^2)
      (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).hi ≤
      thetaLastCellBinUpper i k := by
  have h : (thetaGammaMemoUpperNineBin thetaLastCellWExp 8 (thetaLastCellB^2)
      (thetaLastCellBinStart i) (thetaLastCellBinEnd i) k).hi ≤
      thetaLastCellBinUpper i k :=
    (thetaLastCellGammaAllBins_checked i k).2
  rw [thetaGammaMemoUpperNineBin_eq thetaLastCellWExp thetaLastCellWExp_eq] at h
  exact h

/-- Add the local checked lower bounds. No numerical evaluation of
the closed integral grid is performed by this proof. -/
theorem thetaLastCellLowerSum_bound (k : Fin 9) :
    thetaLastCellBinLowerSum k ≤
      (thetaGammaLowerGridBox k.val (thetaLastCellA^2)
        (thetaGammaAutoRootGrid 8 (thetaLastCellA^2)) 0 thetaLastCellGrid).lo := by
  rw [thetaLastCellGrid_explicit]
  simp only [thetaGammaLowerGridBox, QInterval.add, QInterval.point]
  exact add_le_add (thetaLastCellBinLower_bound (0:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (1:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (2:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (3:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (4:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (5:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (6:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (7:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (8:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (9:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (10:Fin 12) k) (add_le_add (thetaLastCellBinLower_bound (11:Fin 12) k) (le_refl (0:ℚ)))))))))))))

theorem thetaLastCellUpperSum_bound (k : Fin 9) :
    (thetaGammaUpperGridBox k.val (thetaLastCellB^2)
      (thetaGammaAutoRootGrid 8 (thetaLastCellB^2)) 0 thetaLastCellGrid).hi ≤
      thetaLastCellBinUpperSum k := by
  rw [thetaLastCellGrid_explicit]
  simp only [thetaGammaUpperGridBox, QInterval.add, QInterval.point]
  exact add_le_add (thetaLastCellBinUpper_bound (0:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (1:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (2:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (3:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (4:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (5:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (6:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (7:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (8:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (9:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (10:Fin 12) k) (add_le_add (thetaLastCellBinUpper_bound (11:Fin 12) k) (le_refl (0:ℚ)))))))))))))

/-- The sum of the compact bin endpoints and exact analytic tail
encloses the full original endpoint moments. Transfer the existing
already-proved monotone cell enclosure; no new integration lemma. -/
theorem thetaLastCellReplayMoment_containsReal
    (x : ℝ) (hax : (thetaLastCellA:ℝ) ≤ x)
    (hxb : x ≤ (thetaLastCellB:ℝ)) (k : ℕ) (hk : k < 9) :
    QInterval.ContainsReal (thetaLastCellReplayMomentWitness k)
      (thetaAuditedOneWeightedMoment x k) := by
  let K : Fin 9 := ⟨k,hk⟩
  have hfit := thetaLastCellGammaMomentSums_checked K
  have hlo : (thetaLastCellGammaFastBox K).lo ≤
      (thetaGammaAutoMomentBox 8 k thetaLastCellA thetaLastCellGrid).lo := by
    simpa only [thetaLastCellGammaFastBox, thetaGammaAutoMomentBox,
      thetaGammaAutoFullMomentGridBox, thetaGammaWeightedExactTailBox,
      QInterval.add, add_zero, K] using thetaLastCellLowerSum_bound K
  have hhi : (thetaGammaAutoMomentBox 8 k thetaLastCellB thetaLastCellGrid).hi ≤
      (thetaLastCellGammaFastBox K).hi := by
    simp only [thetaLastCellGammaFastBox, thetaGammaAutoMomentBox,
      thetaGammaAutoFullMomentGridBox, thetaGammaWeightedExactTailBox,
      QInterval.add, thetaLastCellGrid_last, thetaLastCellWExp_eq, K]
    exact add_le_add (thetaLastCellUpperSum_bound K) le_rfl
  have hA := thetaGammaAutoMomentBox_containsReal_of_check
    8 k thetaLastCellA thetaLastCellGrid thetaLastCellGammaA_checked
  have hB := thetaGammaAutoMomentBox_containsReal_of_check
    8 k thetaLastCellB thetaLastCellGrid thetaLastCellGammaB_checked
  have hcell := thetaAuditedOneWeightedMoment_cell_interval
    (thetaLastCellA:ℝ) x (thetaLastCellB:ℝ)
    (by norm_num [thetaLastCellA]) hax hxb (by norm_num [thetaLastCellB])
    k _ _ hA hB
  exact thetaLastCellReplayWiden (hfit.1.trans hlo) (hhi.trans hfit.2) hcell

end W5
