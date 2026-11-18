import Mathlib

/-!
## Exact calculus for one theta summand

The original theta kernel is first integrated term by term. This file
formalizes the local derivative identity used in that integration by
parts. The uniform domination needed to interchange the infinite
sum and improper integral is *not* assumed or proved here.
-/

namespace W5

/-- The elementary derivative underlying the integrated theta kernel. -/
theorem theta_power_exp_hasDerivAt (p y : ℝ) (hy : 0 < y) :
    HasDerivAt
      (fun z : ℝ => z ^ ((5 : ℝ) / 4) * Real.exp (-p*z))
      (((5 : ℝ) / 4) * y ^ ((1 : ℝ) / 4) * Real.exp (-p*y) -
        p * y ^ ((5 : ℝ) / 4) * Real.exp (-p*y)) y := by
  have hpow0 :
      HasDerivAt (fun z : ℝ => z ^ ((5 : ℝ) / 4))
        (((5 : ℝ) / 4) * y ^ ((5 : ℝ) / 4 - 1)) y :=
    Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hy))
  have hpow :
      HasDerivAt (fun z : ℝ => z ^ ((5 : ℝ) / 4))
        (((5 : ℝ) / 4) * y ^ ((1 : ℝ) / 4)) y := by
    convert hpow0 using 1 <;> ring
  have hlin : HasDerivAt (fun z : ℝ => -p*z) (-p) y := by
    simpa using (hasDerivAt_id y).const_mul (-p)
  have hexp :
      HasDerivAt (fun z : ℝ => Real.exp (-p*z))
        (Real.exp (-p*y) * (-p)) y :=
    (Real.hasDerivAt_exp (-p*y)).comp y hlin
  convert hpow.mul hexp using 1 <;> ring

/-- An identity between the theta integrand and the differentiated boundary term. -/
theorem theta_integration_by_parts_integrand (p y : ℝ) (hy : 0 < y) :
    y ^ ((1 : ℝ)/4) * (2*p*y-3) * Real.exp (-p*y) =
      -2 * (((5 : ℝ)/4) * y ^ ((1 : ℝ)/4) * Real.exp (-p*y) -
        p * y ^ ((5 : ℝ)/4) * Real.exp (-p*y)) -
      (1/2 : ℝ) * y ^ ((1 : ℝ)/4) * Real.exp (-p*y) := by
  have hpow : y ^ ((5:ℝ)/4) = y * y ^ ((1:ℝ)/4) := by
    have he : ((5:ℝ)/4) = 1 + ((1:ℝ)/4) := by ring
    rw [he, Real.rpow_add hy, Real.rpow_one]
  rw [hpow]
  ring

end W5
