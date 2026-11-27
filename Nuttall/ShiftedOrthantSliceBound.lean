import Nuttall.OrthantSliceBound
import Nuttall.CentralOrthantMass

namespace Nuttall

open Filter MeasureTheory Set

/-- The open cube's complement restricts a positive coordinate to the upper
tail. The single boundary point has zero Lebesgue measure. -/
private theorem restrict_positive_coordinate_compl {B : ℝ} (hB : 0 < B) :
    (volume.restrict (Ioi (0:ℝ))).restrict (Ioo 0 B)ᶜ = volume.restrict (Ioi B) := by
  rw [Measure.restrict_restrict measurableSet_Ioo.compl]
  have he : (Ioo 0 B)ᶜ ∩ Ioi 0 = Ici B := by
    ext x
    simp only [mem_inter_iff, mem_compl_iff, mem_Ioo, mem_Ioi, mem_Ici]
    constructor
    · rintro ⟨hx, hx₀⟩
      exact le_of_not_gt (fun h => hx ⟨hx₀,h⟩)
    · intro hx
      exact ⟨fun h => (not_lt_of_ge hx) h.2, hB.trans_le hx⟩
  rw [he]
  exact Measure.restrict_congr_set Ioi_ae_eq_Ici.symm

/-- The relative tail estimate may be proved separately on each one-dimensional
section, using ordinary Lebesgue integrals on the two half-lines. -/
theorem integral_shiftedOrthant_compl_le_of_slices {n : ℕ} {B X η : ℝ}
    (hB : 0 < B) (hX : 0 < X) (k : Fin (n+1) → ℕ)
    (hSlice : ∀ i : Fin (n+1), ∀ᵐ v ∂positiveOrthant n,
      let G x := |shiftedOrthantIntegrand X (fun j _ => shiftedMoment (k j)) (i.insertNth x v)|
      (∫ x in Ioi B, G x) ≤ η * ∫ x in Ioi 0, G x) :
    (∫ u in (thetaCentralCube (n+1) B)ᶜ,
      |shiftedOrthantIntegrand X (fun j _ => shiftedMoment (k j)) u| ∂positiveOrthant (n+1)) ≤
      ((n+1:ℕ):ℝ)*η *
        ∫ u, |shiftedOrthantIntegrand X (fun j _ => shiftedMoment (k j)) u| ∂positiveOrthant (n+1) := by
  apply integral_pi_compl_le_of_slices (volume.restrict (Ioi (0:ℝ))) measurableSet_Ioo
    (integrable_shiftedOrthant hX k).abs (fun _ => abs_nonneg _) η
  intro i
  rw [restrict_positive_coordinate_compl hB]
  exact hSlice i

#print axioms integral_shiftedOrthant_compl_le_of_slices

end Nuttall
