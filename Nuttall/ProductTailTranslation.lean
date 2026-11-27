import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

namespace Nuttall

open MeasureTheory Set

private theorem measurePreserving_tail_add (a d : ℝ) :
    MeasurePreserving (MeasurableEquiv.addRight d)
      (volume.restrict (Ici a)) (volume.restrict (Ici (a+d))) := by
  let e := MeasurableEquiv.addRight d
  have hp : MeasurePreserving e volume volume := by
    exact ⟨e.measurable, map_add_right_eq_self volume d⟩
  have hpre : e ⁻¹' Ici (a+d) = Ici a := by
    ext x
    change a+d ≤ x+d ↔ a ≤ x
    exact add_le_add_iff_right d
  simpa only [hpre] using hp.restrict_preimage (s := Ici (a+d)) measurableSet_Ici

/-- Independent translations of the coordinates preserve the integral
when each lower bound is translated by the matching amount. -/
theorem integral_product_tails_add {p : ℕ} (a d : Fin p → ℝ) (F : (Fin p → ℝ) → ℝ) :
    (∫ x : Fin p → ℝ, F (fun i => x i+d i) ∂Measure.pi (fun i => volume.restrict (Ici (a i)))) =
      ∫ u : Fin p → ℝ, F u ∂Measure.pi (fun i => volume.restrict (Ici (a i+d i))) := by
  let e : (Fin p → ℝ) ≃ᵐ (Fin p → ℝ) :=
    MeasurableEquiv.piCongrRight (fun i => MeasurableEquiv.addRight (d i))
  have h : MeasurePreserving e (Measure.pi (fun i => volume.restrict (Ici (a i))))
      (Measure.pi (fun i => volume.restrict (Ici (a i+d i)))) :=
    measurePreserving_pi _ _ (fun i => measurePreserving_tail_add (a i) (d i))
  exact h.integral_comp' F

theorem product_tail_measure_open_eq_closed {p : ℕ} (a : Fin p → ℝ) :
    Measure.pi (fun i => volume.restrict (Ioi (a i))) =
      Measure.pi (fun i => volume.restrict (Ici (a i))) := by
  congr 1
  funext i
  exact Measure.restrict_congr_set Ioi_ae_eq_Ici

/-- Express separate positive lower bounds as a restriction of the common
positive orthant. -/
theorem product_tail_measure_restrict {p : ℕ} (a : Fin p → ℝ) (ha : ∀ i, 0 ≤ a i) :
    (Measure.pi (fun _ : Fin p => volume.restrict (Ioi (0 : ℝ)))).restrict
      (univ.pi (fun i => Ioi (a i))) =
      Measure.pi (fun i => volume.restrict (Ioi (a i))) := by
  rw [Measure.restrict_pi_pi]
  congr 1
  funext i
  exact Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (ha i))

#print axioms integral_product_tails_add

end Nuttall
