import Mathlib.MeasureTheory.Integral.Bochner.Set

namespace Nuttall

open MeasureTheory Set

/-- A nonnegative central region is sufficient when the complementary absolute
mass is strictly less than half of the total absolute mass. -/
theorem integral_pos_of_relative_tail {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {s : Set E} (hs : MeasurableSet s) {f : E → ℝ}
    (hf : Integrable f μ) (hcentral : 0 ≤ᵐ[μ.restrict s] f)
    (hmass : 0 < ∫ x, |f x| ∂μ) {η : ℝ} (hη : η < 1 / 2)
    (htail : (∫ x in sᶜ, |f x| ∂μ) ≤ η * ∫ x, |f x| ∂μ) :
    0 < ∫ x, f x ∂μ := by
  have hcentralEq : (∫ x in s, |f x| ∂μ) = ∫ x in s, f x ∂μ :=
    integral_congr_ae (hcentral.mono (fun x hx => abs_of_nonneg hx))
  have htotal := integral_add_compl hs hf
  have habs := integral_add_compl hs hf.abs
  rw [hcentralEq] at habs
  have hoff := abs_integral_le_integral_abs (μ := μ.restrict sᶜ) (f := f)
  have hneg := le_abs_self (-(∫ x in sᶜ, f x ∂μ))
  rw [abs_neg] at hneg
  have hsmall := mul_lt_mul_of_pos_right hη hmass
  linarith only [htotal, habs, hoff, hneg, htail, hsmall]

#print axioms integral_pos_of_relative_tail

end Nuttall
