import Nuttall.PhiCompactCells

namespace Nuttall

private def psiOneCompactEndpoints : List ℚ :=
  ((List.range 61).map (fun i => 2*(i+1)) ++ [123,124,125,126,127,128]).map
    (fun p => (p:ℚ)/256)

/-- The 67 closed intervals of the preprint's compact rank-seven certificate. -/
def psiOneCompactCells : List (ℚ × ℚ) := adjacentCells 0 psiOneCompactEndpoints

theorem psiOneCompactCells_length : psiOneCompactCells.length = 67 := by decide +kernel

theorem psiOneCompactCells_facts {ab : ℚ × ℚ} (hab : ab ∈ psiOneCompactCells) :
    0 ≤ ab.1 ∧ ab.1 < ab.2 ∧ ab.2 ≤ 1/2 ∧ ab.2-ab.1 ≤ 1/128 := by
  let pass (c : ℚ × ℚ) := decide (0 ≤ c.1 ∧ c.1 < c.2 ∧ c.2 ≤ 1/2 ∧ c.2-c.1 ≤ 1/128)
  have h : psiOneCompactCells.all pass = true := by decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp h ab hab)

theorem psiOneCompactCells_cover {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    ∃ ab ∈ psiOneCompactCells, (ab.1:ℝ) ≤ t ∧ t ≤ (ab.2:ℝ) := by
  have hend : lastEndpoint 0 psiOneCompactEndpoints = 1/2 := by decide +kernel
  have hu : t ≤ (lastEndpoint 0 psiOneCompactEndpoints:ℝ) := by
    simpa only [hend, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using ht₁
  have hl : ((0:ℚ):ℝ) ≤ t := by simpa only [Rat.cast_zero] using ht₀
  rcases adjacentCells_cover 0 psiOneCompactEndpoints hl hu with h₀ | h
  · refine ⟨(0,1/128), by decide +kernel, hl, ?_⟩
    rw [h₀]
    norm_num
  · exact h

#print axioms psiOneCompactCells_facts
#print axioms psiOneCompactCells_cover

end Nuttall
