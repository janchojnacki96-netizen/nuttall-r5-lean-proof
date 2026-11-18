import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Absolute integrability of each theta summand in the y variable

For every p>0 and s>-1, y^s exp(-p*y) is integrable
on (0,infinity), hence also on every [y0,infinity) with y0>0.

This closes the integrability obligation for *individual* positive
theta terms used in integration by parts. Absolute summability over
the index n and the interchange with the infinite sum are still open.
-/

namespace W5

open MeasureTheory

theorem theta_rpow_exp_integrableOn (p s : ℝ)
    (hp : 0 < p) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ => y ^ s * Real.exp (-p*y))
      (Set.Ioi (0:ℝ)) volume := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1:ℝ)) (s := s) (b := p) hs (by norm_num) hp
  simpa only [Real.rpow_one] using h

theorem theta_rpow_exp_integrableOn_tail (p s y0 : ℝ)
    (hp : 0 < p) (hs : -1 < s) (hy0 : 0 < y0) :
    IntegrableOn (fun y : ℝ => y ^ s * Real.exp (-p*y))
      (Set.Ici y0) volume := by
  have h := theta_rpow_exp_integrableOn p s hp hs
  apply h.mono_set
  intro y hy
  exact lt_of_lt_of_le hy0 hy

theorem theta_quarter_and_five_quarters_integrable (p : ℝ)
    (hp : 0 < p) :
    IntegrableOn
        (fun y : ℝ => y ^ ((1:ℝ)/4) * Real.exp (-p*y))
        (Set.Ioi (0:ℝ)) volume ∧
    IntegrableOn
        (fun y : ℝ => y ^ ((5:ℝ)/4) * Real.exp (-p*y))
        (Set.Ioi (0:ℝ)) volume := by
  constructor
  · exact theta_rpow_exp_integrableOn p ((1:ℝ)/4) hp (by norm_num)
  · exact theta_rpow_exp_integrableOn p ((5:ℝ)/4) hp (by norm_num)

end W5
