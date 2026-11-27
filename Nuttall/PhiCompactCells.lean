import Nuttall.PhiCompactInterval

namespace Nuttall

/-- Grid coordinates in units of 13/1024 measured from X=3. -/
private def phiCompactGrid : List ℚ :=
  ([1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20,
    22, 24, 26, 28, 30, 32, 34, 36, 38, 40, 42, 44, 48, 52, 56, 60, 64, 72, 80, 88,
    96, 112, 128, 160, 192, 256, 320, 384, 512, 768, 1024] : List ℚ).map
      (fun k => 3 + 13*k/1024)

private def adjacentCells (a : ℚ) : List ℚ → List (ℚ × ℚ)
  | [] => []
  | b :: l => (a,b) :: adjacentCells b l

private def lastEndpoint (a : ℚ) : List ℚ → ℚ
  | [] => a
  | b :: l => lastEndpoint b l

private theorem adjacentCells_cover {x : ℝ} (a : ℚ) (endpoints : List ℚ)
    (ha : (a:ℝ) ≤ x) (hb : x ≤ (lastEndpoint a endpoints : ℝ)) :
    x = (a:ℝ) ∨ ∃ c ∈ adjacentCells a endpoints, (c.1:ℝ) ≤ x ∧ x ≤ (c.2:ℝ) := by
  induction endpoints generalizing a with
  | nil => exact Or.inl (le_antisymm hb ha)
  | cons b l ih =>
    by_cases h : x ≤ (b:ℝ)
    · exact Or.inr ⟨(a,b), by simp [adjacentCells], ha,h⟩
    · rcases ih b (le_of_not_ge h) hb with he | ⟨c,hc,hl,hu⟩
      · exact (h (le_of_eq he)).elim
      · exact Or.inr ⟨c, List.mem_cons_of_mem _ hc, hl, hu⟩

local instance (a b : ℚ) (p : ℕ) : Decidable (phiCompactCellCheck a b p) := by
  unfold phiCompactCellCheck
  infer_instance

def phiCompactCellPass (c : ℚ × ℚ) : Bool :=
  decide (3 ≤ c.1 ∧ c.2 ≤ 16) &&
    [1,2,3,4].all (fun p => decide (phiCompactCellCheck c.1 c.2 p))

/-- Concrete closed cells used by the compact determinant checker. -/
def phiCompactCells : List (ℚ × ℚ) := adjacentCells 3 phiCompactGrid

/-- The finite certificate to prove by exact arithmetic in the Lean kernel. -/
def phiCompactGridChecked : Prop := phiCompactCells.all phiCompactCellPass = true

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2500000 in
/-- A focused kernel replay of all four determinant checks on the first dense cell. -/
theorem phiCompact_first_cell_pass : phiCompactCellPass (3, 3085/1024) = true := by
  decide +kernel

/-- The rational cells prove the strict signed Wronskians on the compact range 3 ≤ X ≤ 16. -/
theorem phiCompactWronskian_pos (hgrid : phiCompactGridChecked) {p : ℕ} (hp₁ : 1 ≤ p) (hp₄ : p ≤ 4) (t : ℝ)
    (ht₃ : 3 ≤ phiThetaCoordinate t) (ht₁₆ : phiThetaCoordinate t ≤ 16) :
    0 < kernelMinorSign p * wronskian W5.Phi p t := by
  have he : lastEndpoint 3 phiCompactGrid = 16 := by decide +kernel
  have hu : phiThetaCoordinate t ≤ (lastEndpoint 3 phiCompactGrid:ℝ) := by
    simpa only [he, Rat.cast_ofNat] using ht₁₆
  have h₃ : (↑(3:ℚ):ℝ) ≤ phiThetaCoordinate t := by simpa using ht₃
  obtain ⟨c, hc, h1, h2⟩ : ∃ c ∈ adjacentCells 3 phiCompactGrid,
      (c.1:ℝ) ≤ phiThetaCoordinate t ∧ phiThetaCoordinate t ≤ (c.2:ℝ) := by
    rcases adjacentCells_cover 3 phiCompactGrid h₃ hu with hx | hc
    · refine ⟨(3, 3085/1024), ?_, h₃, ?_⟩
      · exact List.mem_cons_self
      · rw [hx]
        norm_num
    · exact hc
  have hC := List.all_eq_true.mp hgrid c hc
  have hsplit := Bool.and_eq_true_iff.mp hC
  obtain ⟨h3,h16⟩ := of_decide_eq_true hsplit.1
  have hm : p ∈ [1,2,3,4] := by interval_cases p <;> decide
  exact phiCompactCellCheck_sound hp₄ t h3 h16 h1 h2
    (of_decide_eq_true (List.all_eq_true.mp hsplit.2 p hm))

#print axioms phiCompact_first_cell_pass
#print axioms phiCompactWronskian_pos

end Nuttall
