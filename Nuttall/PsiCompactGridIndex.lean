import Nuttall.PsiCompactGridSigns

namespace Nuttall

/-- The cell at the index of its corresponding matrix certificate. -/
def psiOneCompactCell (i : Fin 67) : ℚ × ℚ :=
  psiOneCompactCells[i.val]'(by simpa only [psiOneCompactCells_length] using i.isLt)

theorem psiOneCompactCell_mem (i : Fin 67) : psiOneCompactCell i ∈ psiOneCompactCells :=
  List.getElem_mem (by simpa only [psiOneCompactCells_length] using i.isLt)

theorem psiOneCompactCell_sixty : psiOneCompactCell 60 = (15/32, 61/128) := by
  decide +kernel

theorem psiOneCompactCell_geometry (i : Fin 67) :
    let c : ℝ := psiOneCellCenter (psiOneCompactCell i)
    let h : ℝ := psiOneCellRadius (psiOneCompactCell i)
    0 ≤ c-h ∧ c+h ≤ 2 ∧ 0 ≤ h ∧ h ≤ 1/256 := by
  let ab := psiOneCompactCell i
  obtain ⟨ha, hab, hb, hw⟩ := psiOneCompactCells_facts (psiOneCompactCell_mem i)
  have ha' : 0 ≤ (ab.1:ℝ) := by exact_mod_cast ha
  have hb' : (ab.2:ℝ) ≤ 1/2 := by exact_mod_cast hb
  have hwidth : 0 < (ab.2:ℝ)-(ab.1:ℝ) := by exact_mod_cast sub_pos.mpr hab
  have hwidth' : (ab.2:ℝ)-(ab.1:ℝ) ≤ 1/128 := by exact_mod_cast hw
  simp only [psiOneCellCenter, psiOneCellRadius, Rat.cast_add, Rat.cast_sub, Rat.cast_div,
    Rat.cast_ofNat]
  exact ⟨by linarith only [ha'], by linarith only [hb'],
    by linarith only [hwidth], by linarith only [hwidth']⟩

/-- Assemble a certificate indexed by the same finite type as the matrix data. -/
theorem psiOne_compact_indexed_grid_signed_wronskians
    (hcell : ∀ (i : Fin 67) (p : ℕ), p ≤ 7 → ∀ v : ℝ, |v| ≤ 1 →
      0 < kernelMinorSign p * wronskian (psi 1) p
        ((psiOneCellCenter (psiOneCompactCell i):ℝ)+(psiOneCellRadius (psiOneCompactCell i):ℝ)*v))
    (p : ℕ) (hp : p ≤ 7) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1/2) :
    0 < kernelMinorSign p * wronskian (psi 1) p t := by
  refine psiOne_compact_grid_signed_wronskians ?_ p hp t ht₀ ht₁
  intro ab hab n hn v hv
  obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hab
  let i : Fin 67 := ⟨j, by simpa only [psiOneCompactCells_length] using hj⟩
  have hi : psiOneCompactCell i = ab := he
  simpa only [hi] using hcell i n hn v hv

#print axioms psiOne_compact_indexed_grid_signed_wronskians

end Nuttall
