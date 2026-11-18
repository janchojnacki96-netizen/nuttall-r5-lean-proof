import W5.ThetaIntegralStrictPositivity
import W5.PhiFirstDerivative

/-!
# Integrability of the original theta kernel on every upper half-line

The strict positivity theorem for the original Psi1 allows us to infer
integrability on [t,infinity) for t>=0: in Mathlib's Bochner convention,
an otherwise nonintegrable function would have integral zero.

Continuity of Phi (proved via termwise theta differentiation)
then extends integrability to [t,infinity) for EVERY real t by
adding a compact interval. This will be used in the fundamental
theorem of calculus for Psi1.
-/

namespace W5

open MeasureTheory

/-- Actual absolute integrability of the original theta kernel on
every nonnegative half-line. -/
theorem Phi_integrableOn_Ici_of_nonneg (t : ℝ) (ht : 0 ≤ t) :
    IntegrableOn Phi (Set.Ici t) (volume : Measure ℝ) := by
  apply Integrable.of_integral_ne_zero
  have hp := Psi1_pos t ht
  change 0 < (∫ s in Set.Ici t, Phi s) at hp
  exact ne_of_gt hp

/-- Actual absolute integrability on every upper half-line, including
those with negative lower endpoints. -/
theorem Phi_integrableOn_Ici_all (t : ℝ) :
    IntegrableOn Phi (Set.Ici t) (volume : Measure ℝ) := by
  have h0 : IntegrableOn Phi (Set.Ici (0:ℝ)) (volume : Measure ℝ) :=
    Phi_integrableOn_Ici_of_nonneg 0 (by norm_num)
  have hcompact :
      IntegrableOn Phi (Set.Icc (min t 0) 0) (volume : Measure ℝ) :=
    Phi_differentiable.continuous.integrableOn_Icc
  have hunion :
      IntegrableOn Phi (Set.Icc (min t 0) 0 ∪ Set.Ici 0)
        (volume : Measure ℝ) :=
    integrableOn_union.mpr ⟨hcompact, h0⟩
  apply hunion.mono_set
  intro s hs
  change t ≤ s at hs
  by_cases hsmall : s ≤ 0
  · exact Or.inl ⟨(min_le_left t 0).trans hs, hsmall⟩
  · exact Or.inr (le_of_lt (lt_of_not_ge hsmall))

theorem Phi_integrableOn_Ioi_all (t : ℝ) :
    IntegrableOn Phi (Set.Ioi t) (volume : Measure ℝ) :=
  (Phi_integrableOn_Ici_all t).mono_set Set.Ioi_subset_Ici_self

end W5
