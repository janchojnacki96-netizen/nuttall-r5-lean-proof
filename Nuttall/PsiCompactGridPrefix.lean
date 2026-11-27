import Nuttall.PsiCompactCells

namespace Nuttall

private def psiOneCompactPrefixEndpoints : List ℚ :=
  (List.range 53).map (fun i => ((i+1:ℕ):ℚ)/128)

/-- The prefix of the compact grid needed before the analytic tail. -/
def psiOneCompactPrefix : List (ℚ × ℚ) := psiOneCompactCells.take 53

theorem psiOneCompactPrefix_cover {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 53/128) :
    ∃ ab ∈ psiOneCompactPrefix, (ab.1:ℝ) ≤ t ∧ t ≤ (ab.2:ℝ) := by
  have hc : adjacentCells 0 psiOneCompactPrefixEndpoints = psiOneCompactPrefix := by decide +kernel
  have he : lastEndpoint 0 psiOneCompactPrefixEndpoints = 53/128 := by decide +kernel
  have hl : ((0:ℚ):ℝ) ≤ t := by simpa only [Rat.cast_zero] using ht₀
  have hu : t ≤ (lastEndpoint 0 psiOneCompactPrefixEndpoints:ℝ) := by
    simpa only [he, Rat.cast_div, Rat.cast_ofNat] using ht₁
  rcases adjacentCells_cover 0 psiOneCompactPrefixEndpoints hl hu with h₀ | ⟨c, hm, ha, hb⟩
  · refine ⟨(0,1/128), by decide +kernel, hl, ?_⟩
    rw [h₀]
    norm_num
  · exact ⟨c, hc ▸ hm, ha, hb⟩

#print axioms psiOneCompactPrefix_cover

end Nuttall
