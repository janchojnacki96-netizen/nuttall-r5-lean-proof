import Nuttall.PsiCompactCells
import Nuttall.PsiCompactCellSigns

namespace Nuttall

def psiOneCellCenter (ab : ℚ × ℚ) : ℚ := (ab.1+ab.2)/2
def psiOneCellRadius (ab : ℚ × ℚ) : ℚ := (ab.2-ab.1)/2

/-- Glue the compact cells, preserving the signs at both endpoints. -/
theorem psiOne_compact_grid_signed_wronskians
    (hcell : ∀ ab ∈ psiOneCompactCells, ∀ p ≤ 7, ∀ v : ℝ, |v| ≤ 1 →
      0 < kernelMinorSign p * wronskian (psi 1) p
        ((psiOneCellCenter ab:ℝ)+(psiOneCellRadius ab:ℝ)*v))
    (p : ℕ) (hp : p ≤ 7) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  obtain ⟨ab, hab, hL, hU⟩ := psiOneCompactCells_cover ht₀ ht₁
  have hab' : (ab.1:ℝ) < (ab.2:ℝ) := by
    exact_mod_cast (psiOneCompactCells_facts hab).2.1
  let c : ℝ := psiOneCellCenter ab
  let h : ℝ := psiOneCellRadius ab
  have hcL : c-h = (ab.1:ℝ) := by
    dsimp [c, h, psiOneCellCenter, psiOneCellRadius]
    push_cast
    ring
  have hcU : c+h = (ab.2:ℝ) := by
    dsimp [c, h, psiOneCellCenter, psiOneCellRadius]
    push_cast
    ring
  have hh : 0 < h := by linarith only [hab', hcL, hcU]
  let v := (t-c)/h
  have hv : |v| ≤ 1 := by
    apply abs_le.mpr
    constructor
    · apply (le_div_iff₀ hh).2
      linarith only [hL, hcL]
    · apply (div_le_iff₀ hh).2
      linarith only [hU, hcU]
  have hev : c+h*v = t := by
    dsimp [v]
    field_simp [hh.ne'] <;> ring
  have hsign := hcell ab hab p hp v hv
  change 0 < kernelMinorSign p * wronskian (psi 1) p (c+h*v) at hsign
  rwa [hev] at hsign

#print axioms psiOne_compact_grid_signed_wronskians

end Nuttall
