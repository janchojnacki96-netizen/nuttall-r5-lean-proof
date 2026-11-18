import W5.ThetaImproperIntegrationByParts
import W5.ThetaGammaScaling

/-!
# The exact one-square term of the integrated theta series

This is the single summand appearing in the certificate's
closed expression for Psi1, after the y-coordinate substitution.

It is a genuine Lean theorem (not an assumption), provided the
two imported improper-integral and scaling lemmas compile.

The remaining analytic obligation is to identify the whole Psi1
defined in the original t-coordinate with the sum of these terms.
-/

namespace W5

open MeasureTheory

theorem theta_single_square_closed_form (p a : ℝ)
    (hp : 0 < p) (ha : 0 < a) :
    (∫ y in Set.Ioi a,
      y ^ ((1:ℝ)/4)*(2*p*y-3)*Real.exp (-p*y)) =
      2*a ^ ((5:ℝ)/4) *
        (Real.exp (-p*a) -
         (1/4:ℝ) *
           (∫ v in Set.Ioi (1:ℝ),
             v ^ ((1:ℝ)/4)*Real.exp (-p*a*v))) := by
  rw [theta_single_summand_improper_formula p a hp ha]
  rw [theta_quarter_integral_scale p a ha]
  ring

end W5
