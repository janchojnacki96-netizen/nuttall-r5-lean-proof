import W5.ThetaExpSubstitution
import W5.ThetaIntegratedClosedForm

/-!
# Identify the original Psi1 density with the exact integrated theta series

This is the missing analytic bridge between the original t-coordinate
definition of Psi1 and the already verified y-coordinate series.
The formula is proved for all t >= 0; it does NOT assert the
order-five Wronskian sign theorem or validate numerical pivot signs.
-/

namespace W5

open MeasureTheory

private theorem theta_exp_four_quarter (t : ℝ) :
    Real.exp (4*t) ^ ((1:ℝ)/4) = Real.exp t := by
  rw [← Real.exp_mul]
  congr 1
  ring

private theorem theta_density_prefactor (t : ℝ) :
    (Real.pi * Real.exp (5*t)) /
        (Real.pi * Real.exp (4*t)) ^ ((1:ℝ)/4) =
      ((4:ℝ) * Real.pi * Real.exp (4*t)) *
        (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) := by
  have hquarter :
      (Real.pi * Real.exp (4*t)) ^ ((1:ℝ)/4) =
        Real.pi ^ ((1:ℝ)/4) * Real.exp t := by
    rw [Real.mul_rpow (le_of_lt Real.pi_pos)
      (le_of_lt (Real.exp_pos (4*t)))]
    exact congrArg (fun z : ℝ => Real.pi ^ ((1:ℝ)/4) * z)
      (theta_exp_four_quarter t)
  have hfive :
      Real.exp (5*t) = Real.exp (4*t) * Real.exp t := by
    rw [show (5:ℝ)*t = 4*t + t by ring, Real.exp_add]
  have hp : Real.pi ^ ((1:ℝ)/4) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have he : Real.exp t ≠ 0 := ne_of_gt (Real.exp_pos t)
  rw [hquarter, hfive]
  field_simp [hp, he] <;> ring

/-- The inverse-coordinate density equals the genuine theta y-series
at every point y = pi * exp(4*t). -/
theorem thetaOriginalDensity_at_exp_eq_tsum (t : ℝ) :
    thetaOriginalDensity (Real.pi * Real.exp (4*t)) =
      (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
        (∑' n : ℕ,
           thetaYIntegrand n (Real.pi * Real.exp (4*t))) := by
  have hfac :
      (4:ℝ) * Real.pi * Real.exp (4*t) ≠ 0 :=
    ne_of_gt (by positivity)
  have hjoined :
      ((4:ℝ) * Real.pi * Real.exp (4*t)) *
        thetaOriginalDensity (Real.pi * Real.exp (4*t)) =
      ((4:ℝ) * Real.pi * Real.exp (4*t)) *
        ((1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
          (∑' n : ℕ,
             thetaYIntegrand n (Real.pi * Real.exp (4*t)))) := by
    calc
      _ = Phi t := thetaOriginalDensity_at_exp t
      _ = (Real.pi * Real.exp (5*t) /
          (Real.pi * Real.exp (4*t)) ^ ((1:ℝ)/4)) *
            (∑' n : ℕ,
               thetaYIntegrand n (Real.pi * Real.exp (4*t))) :=
        Phi_eq_thetaY_tsum t
      _ = _ := by
        rw [theta_density_prefactor t]
        ring
  exact mul_left_cancel₀ hfac hjoined

/-- Pointwise identification of the inverse density with the theta
sum on the entire positive y half-line. -/
theorem thetaOriginalDensity_eq_tsum (y : ℝ) (hy : 0 < y) :
    thetaOriginalDensity y =
      (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
        (∑' n : ℕ, thetaYIntegrand n y) := by
  let t : ℝ := Real.log (y / Real.pi) / 4
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hydiv : 0 < y / Real.pi := div_pos hy Real.pi_pos
  have hcoord : Real.pi * Real.exp (4*t) = y := by
    dsimp [t]
    rw [show (4:ℝ) * (Real.log (y / Real.pi) / 4) =
        Real.log (y / Real.pi) by ring, Real.exp_log hydiv]
    field_simp [hpi] <;> ring
  simpa only [hcoord] using thetaOriginalDensity_at_exp_eq_tsum t

/-- Original Psi1 as the actual integral of the y-theta series. -/
theorem Psi1_eq_thetaY_integral (t : ℝ) :
    Psi1 t =
      (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
        (∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
          ∑' n : ℕ, thetaYIntegrand n y) := by
  have hy0 : 0 < Real.pi * Real.exp (4*t) :=
    mul_pos Real.pi_pos (Real.exp_pos _)
  calc
    Psi1 t =
        ∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
          thetaOriginalDensity y :=
      Psi1_eq_integral_thetaOriginalDensity t
    _ = ∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
          (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
            (∑' n : ℕ, thetaYIntegrand n y) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      exact thetaOriginalDensity_eq_tsum y (lt_trans hy0 hy)
    _ = _ := by rw [integral_const_mul]

/-- Exact closed theta-series formula for ORIGINAL Psi1 on t >= 0.
This uses the proved y-series/integral interchange and gamma tail. -/
theorem Psi1_eq_theta_closed_form (t : ℝ) (ht : 0 ≤ t) :
    Psi1 t =
      (1 / ((4:ℝ) * Real.pi ^ ((1:ℝ)/4))) *
      (∑' n : ℕ,
        2 * (n:ℝ)^2 *
          (Real.pi * Real.exp (4*t)) ^ ((5:ℝ)/4) *
            (Real.exp (-(n:ℝ)^2 * (Real.pi * Real.exp (4*t))) -
             (1/4:ℝ) *
               (∫ v in Set.Ioi (1:ℝ),
                 v ^ ((1:ℝ)/4) *
                   Real.exp (-(n:ℝ)^2 *
                     (Real.pi * Real.exp (4*t))*v)))) := by
  have h4t : 0 ≤ (4:ℝ)*t := by positivity
  have hexp : (1:ℝ) ≤ Real.exp (4*t) := by
    linarith [Real.add_one_le_exp (4*t)]
  have hpi : (1:ℝ) ≤ Real.pi := by
    linarith [Real.pi_gt_three]
  have hy0 : (1:ℝ) ≤ Real.pi * Real.exp (4*t) := by
    calc
      (1:ℝ) = 1*1 := by ring
      _ ≤ Real.pi * Real.exp (4*t) :=
        mul_le_mul hpi hexp (by norm_num) (le_of_lt Real.pi_pos)
  have hclosed :
      (∫ y in Set.Ioi (Real.pi * Real.exp (4*t)),
        ∑' n : ℕ, thetaYIntegrand n y) =
      ∑' n : ℕ,
        2 * (n:ℝ)^2 *
          (Real.pi * Real.exp (4*t)) ^ ((5:ℝ)/4) *
            (Real.exp (-(n:ℝ)^2 * (Real.pi * Real.exp (4*t))) -
             (1/4:ℝ) *
               (∫ v in Set.Ioi (1:ℝ),
                 v ^ ((1:ℝ)/4) *
                   Real.exp (-(n:ℝ)^2 *
                     (Real.pi * Real.exp (4*t))*v))) := by
    simpa only [MeasureTheory.integral_Ici_eq_integral_Ioi] using
      (thetaY_integral_tsum_closed_form
        (Real.pi * Real.exp (4*t)) hy0)
  rw [Psi1_eq_thetaY_integral, hclosed]

end W5
