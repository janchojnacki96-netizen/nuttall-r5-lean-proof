import W5.ThetaFiniteIntegrationByParts
import W5.ThetaTermIntegrability
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Fundamental theorem of calculus at infinity for a theta summand

A concrete theorem about the original boundary primitive
  G(y) = y^(5/4) exp(-p*y), p>0,
whose derivative is integrable on (a,infinity).
It rigorously evaluates the improper integral of G' and uses
the proved limit G(y)->0.

This does NOT yet assert the full Psi1 transformation:
the t-to-y Jacobian and the infinite theta-series identification
must be connected to the matrix coefficients separately.
-/

namespace W5

open MeasureTheory Filter

theorem theta_boundary_integral_infinite
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    (∫ y in Set.Ioi a,
       ((5:ℝ)/4) *
         (y ^ ((1:ℝ)/4) * Real.exp (-p*y)) -
       p * (y ^ ((5:ℝ)/4) * Real.exp (-p*y))) =
      -a ^ ((5:ℝ)/4) * Real.exp (-p*a) := by
  have hs : Set.Ioi a ⊆ Set.Ioi (0:ℝ) := by
    intro y hy
    exact lt_trans ha hy
  have h1 : IntegrableOn
      (fun y : ℝ => y ^ ((1:ℝ)/4) * Real.exp (-p*y))
      (Set.Ioi a) volume :=
    (theta_rpow_exp_integrableOn p ((1:ℝ)/4) hp
      (by norm_num)).mono_set hs
  have h5 : IntegrableOn
      (fun y : ℝ => y ^ ((5:ℝ)/4) * Real.exp (-p*y))
      (Set.Ioi a) volume :=
    (theta_rpow_exp_integrableOn p ((5:ℝ)/4) hp
      (by norm_num)).mono_set hs
  have hint : IntegrableOn
      (fun y : ℝ =>
        ((5:ℝ)/4) * (y ^ ((1:ℝ)/4) * Real.exp (-p*y)) -
        p * (y ^ ((5:ℝ)/4) * Real.exp (-p*y)))
      (Set.Ioi a) volume :=
    (h1.const_mul ((5:ℝ)/4)).sub (h5.const_mul p)
  have hderiv : ∀ y ∈ Set.Ici a,
      HasDerivAt
        (fun z : ℝ => z ^ ((5:ℝ)/4) * Real.exp (-p*z))
        (((5:ℝ)/4) * (y ^ ((1:ℝ)/4) * Real.exp (-p*y)) -
          p * (y ^ ((5:ℝ)/4) * Real.exp (-p*y))) y := by
    intro y hy
    have h := theta_power_exp_hasDerivAt p y
      (lt_of_lt_of_le ha hy)
    convert h using 1 <;> ring
  have hlim := theta_boundary_tendsto_zero p hp
  have hFTC := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto'
    hderiv hint hlim
  simpa only [zero_sub] using hFTC

end W5
