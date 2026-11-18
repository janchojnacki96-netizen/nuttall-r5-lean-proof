import W5.ThetaImproperBoundaryIntegral
import W5.ThetaTermIntegrability

/-!
# Actual improper integration by parts for a theta summand

For 0<a and 0<p, this theorem computes the improper integral
of y^(1/4) (2*p*y-3) exp(-p*y) on (a,+infty) as a boundary term
minus a simpler integrable term.

This is still only the individual square-index integral. The
change of coordinates from the original Psi1 and the Taylor
coefficient identities require additional formal work.
-/

namespace W5

open MeasureTheory

theorem theta_single_summand_improper_formula
    (p a : ℝ) (hp : 0 < p) (ha : 0 < a) :
    (∫ y in Set.Ioi a,
       y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)) =
      2*a ^ ((5:ℝ)/4)*Real.exp (-p*a) -
      (1/2:ℝ) *
        (∫ y in Set.Ioi a,
          y ^ ((1:ℝ)/4) * Real.exp (-p*y)) := by
  let F : ℝ → ℝ :=
    fun y => y ^ ((1:ℝ)/4) * Real.exp (-p*y)
  let D : ℝ → ℝ :=
    fun y => ((5:ℝ)/4) * (y ^ ((1:ℝ)/4) * Real.exp (-p*y)) -
      p * (y ^ ((5:ℝ)/4) * Real.exp (-p*y))
  have hs : Set.Ioi a ⊆ Set.Ioi (0:ℝ) := by
    intro y hy
    exact lt_trans ha hy
  have hF : IntegrableOn F (Set.Ioi a) volume :=
    (theta_rpow_exp_integrableOn p ((1:ℝ)/4) hp
      (by norm_num)).mono_set hs
  have h5 : IntegrableOn
      (fun y : ℝ => y ^ ((5:ℝ)/4) * Real.exp (-p*y))
      (Set.Ioi a) volume :=
    (theta_rpow_exp_integrableOn p ((5:ℝ)/4) hp
      (by norm_num)).mono_set hs
  have hD : IntegrableOn D (Set.Ioi a) volume :=
    (hF.const_mul ((5:ℝ)/4)).sub (h5.const_mul p)
  have hpoint : ∀ y ∈ Set.Ioi a,
      y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y) =
        (-2:ℝ)*D y - (1/2:ℝ)*F y := by
    intro y hy
    have h := theta_integration_by_parts_integrand p y
      (lt_trans ha hy)
    dsimp only [D,F]
    rw [h]
    ring
  have hcongr :
      (∫ y in Set.Ioi a,
        y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)) =
      (∫ y in Set.Ioi a, (-2:ℝ)*D y - (1/2:ℝ)*F y) := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    exact hpoint y hy
  have hlinear :
      (∫ y in Set.Ioi a, (-2:ℝ)*D y - (1/2:ℝ)*F y) =
        (-2:ℝ)*(∫ y in Set.Ioi a, D y) -
        (1/2:ℝ)*(∫ y in Set.Ioi a, F y) := by
    rw [integral_sub (hD.const_mul (-2)) (hF.const_mul ((1/2:ℝ))),
      integral_const_mul, integral_const_mul]
  have hboundary :
      (∫ y in Set.Ioi a, D y) =
        -a ^ ((5:ℝ)/4)*Real.exp (-p*a) :=
    theta_boundary_integral_infinite p a hp ha
  calc
    (∫ y in Set.Ioi a,
       y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y)) =
        (∫ y in Set.Ioi a, (-2:ℝ)*D y - (1/2:ℝ)*F y) := hcongr
    _ = (-2:ℝ)*(∫ y in Set.Ioi a, D y) -
        (1/2:ℝ)*(∫ y in Set.Ioi a, F y) := hlinear
    _ = 2*a ^ ((5:ℝ)/4)*Real.exp (-p*a) -
      (1/2:ℝ) * (∫ y in Set.Ioi a,
        y ^ ((1:ℝ)/4)*Real.exp (-p*y)) := by
      rw [hboundary]
      dsimp only [F]
      ring

end W5
