import Nuttall.PsiGridJetBoxes
import Nuttall.PsiFirstCellSeed
import Mathlib.Data.Rat.Floor

namespace Nuttall

open W5

private def firstCellGridTime (i : ℕ) : ℚ := 1/256 + (i:ℚ)*(1/32)
def firstCellGridSeed : QInterval := ⟨0, 1/10^7⟩
private def firstCellJetRound (I : QInterval) : QInterval :=
  ⟨(⌊I.lo*10^23⌋ : ℤ) / (10:ℚ)^23, (⌈I.hi*10^23⌉ : ℤ) / (10:ℚ)^23⟩

private theorem firstCellJetRound_containsReal {I : QInterval} {x : ℝ}
    (h : I.ContainsReal x) : (firstCellJetRound I).ContainsReal x := by
  have hL : (firstCellJetRound I).lo ≤ I.lo :=
    (div_le_iff₀ (by positivity)).mpr (Int.floor_le _)
  have hU : I.hi ≤ (firstCellJetRound I).hi :=
    (le_div_iff₀ (by positivity)).mpr (Int.le_ceil _)
  exact ⟨(Rat.cast_mono hL).trans h.1, h.2.trans (Rat.cast_mono hU)⟩

def firstCellGridJets (i j : ℕ) : QInterval :=
  firstCellJetRound (psiGridPhiJetBox (firstCellGridTime i) j 8)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
private theorem firstCellGridExpChecks (i : ℕ) (hi : i < 16) :
    psiGridExpChecks (firstCellGridTime i) := by
  interval_cases i <;> decide +kernel

private theorem firstCellGridJets_containsReal (i j : ℕ) (hi : i < 16) :
    (firstCellGridJets i j).ContainsReal
      (iteratedDeriv j Phi (1/256 + (i:ℝ)*(1/32))) := by
  have hiR : (i:ℚ) ≤ 16 := by exact_mod_cast hi.le
  have ht₀ : 0 ≤ firstCellGridTime i := by unfold firstCellGridTime; positivity
  have ht₂ : firstCellGridTime i ≤ 2 := by unfold firstCellGridTime; linarith only [hiR]
  have h := psiGridPhiJetBox_containsReal ht₀ ht₂ (firstCellGridExpChecks i hi) j 8 (by decide)
  apply firstCellJetRound_containsReal
  simpa only [firstCellGridTime, Rat.cast_add, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

/-- The actual center interval is obtained by 16 backwards Taylor panels
from the shifted right endpoint 129/256. -/
def psiOneFirstCellCornerBox : QInterval :=
  psiOneUniformGridBox firstCellGridSeed firstCellGridJets 20 (1/32) 0 16

theorem psiOne_first_cell_corner_containsReal :
    psiOneFirstCellCornerBox.ContainsReal (psi 1 (1/256)) := by
  have hseed : firstCellGridSeed.ContainsReal (psi 1 (129/256)) := by
    have h := psi_one_short_seed_bounds (t := (129:ℝ)/256) (by norm_num)
    simpa only [QInterval.ContainsReal, firstCellGridSeed, Rat.cast_zero, Rat.cast_div,
      Rat.cast_pow, Rat.cast_one, Rat.cast_ofNat] using h
  have h := psiOneUniformGridBox_containsReal firstCellGridSeed firstCellGridJets 20
    (a := (1:ℝ)/256) (h := (1:ℚ)/32) (by norm_num) (by norm_num) 0 16
    (by norm_num) (by norm_num; exact hseed) (by
      intro i hi j _
      rw [Finset.mem_Ico] at hi
      simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using
        firstCellGridJets_containsReal i j hi.2)
  simpa only [psiOneFirstCellCornerBox, Nat.cast_zero, zero_mul, add_zero] using h

#print axioms psiOne_first_cell_corner_containsReal

end Nuttall
