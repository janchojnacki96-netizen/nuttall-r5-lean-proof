import W5.SingleSummandCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Finite-interval boundary identity for the theta kernel

A genuine application of the second fundamental theorem of calculus
to y^(5/4) * exp(-p*y) on a positive interval [a,b].
Unlike the earlier derivative-only lemma, this proves an equality
between an integral and boundary values.

It is still FINITE-interval: passage b -> infinity and the original
t↦y change of variables are separate analytic obligations.
-/

namespace W5

open MeasureTheory intervalIntegral

theorem theta_boundary_integral_finite
    (p a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    (∫ y in a..b,
       ((5:ℝ)/4) * y ^ ((1:ℝ)/4) * Real.exp (-p*y) -
       p * y ^ ((5:ℝ)/4) * Real.exp (-p*y)) =
      b ^ ((5:ℝ)/4) * Real.exp (-p*b) -
      a ^ ((5:ℝ)/4) * Real.exp (-p*a) := by
  have hderiv : ∀ y ∈ Set.uIcc a b,
      HasDerivAt
        (fun z : ℝ => z ^ ((5:ℝ)/4) * Real.exp (-p*z))
        (((5:ℝ)/4)*y^((1:ℝ)/4)*Real.exp (-p*y) -
          p*y^((5:ℝ)/4)*Real.exp (-p*y)) y := by
    intro y hy
    have hya : a ≤ y := ((Set.uIcc_of_le hab).mp hy).1
    exact theta_power_exp_hasDerivAt p y (lt_of_lt_of_le ha hya)
  have hc1 : Continuous (fun y : ℝ => y ^ ((1:ℝ)/4)) :=
    Real.continuous_rpow_const (by norm_num)
  have hc5 : Continuous (fun y : ℝ => y ^ ((5:ℝ)/4)) :=
    Real.continuous_rpow_const (by norm_num)
  have he : Continuous (fun y : ℝ => Real.exp (-p*y)) := by
    fun_prop
  have hc : Continuous (fun y : ℝ =>
      ((5:ℝ)/4)*y^((1:ℝ)/4)*Real.exp (-p*y) -
        p*y^((5:ℝ)/4)*Real.exp (-p*y)) := by
    exact ((continuous_const.mul hc1).mul he).sub
      ((continuous_const.mul hc5).mul he)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    hderiv (hc.intervalIntegrable a b)

end W5
