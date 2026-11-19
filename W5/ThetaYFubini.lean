import W5.ThetaSeparableFubini
import W5.ThetaMajorantWeights

/-!
# The theta y-integrand: Fubini for the genuine square-index series

For y0>=1, the sum of the terms
  n²*y^(1/4)*(2*n²*y-3)*exp(-n²*y)
can be exchanged with the integral over y in [y0,infinity).

Proof scheme: a finite-rank majorant with summable Gaussian
coefficients (in n) and an integrable gamma weight (in y),
then Mathlib's dominated convergence for countable series.

This result is specifically for the y-transformed integrand.
Connecting it to the original improper integral defining Psi1
requires the change-of-variables theorem, still separate.
-/

namespace W5

open MeasureTheory

noncomputable def thetaYIntegrand (n : ℕ) (y : ℝ) : ℝ :=
  let p : ℝ := (n : ℝ)^2
  p * (y ^ ((1:ℝ)/4) * (2*p*y-3) * Real.exp (-p*y))

theorem thetaYIntegrand_bound (n : ℕ) (y y0 : ℝ)
    (hy0 : 1 ≤ y0) (hy : y0 ≤ y) :
    |thetaYIntegrand n y| ≤
      ((5:ℝ) * (n:ℝ)^4 * Real.exp (-(n:ℝ)^2*y0/2)) *
        (y ^ (2:ℝ) * Real.exp (-y/2)) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaYIntegrand]
  · have hn1 : 1 ≤ n := by omega
    have hn1r : (1:ℝ) ≤ n := by exact_mod_cast hn1
    have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
      nlinarith [sq_nonneg ((n:ℝ)-1)]
    have hp0 : (0:ℝ) ≤ (n:ℝ)^2 := sq_nonneg _
    have h := theta_integrand_abs_split_rpow
      ((n:ℝ)^2) y y0 hp hy0 hy
    simp only [thetaYIntegrand] 
    rw [abs_mul, abs_of_nonneg hp0]
    calc
      (n:ℝ)^2 *
          |y ^ ((1:ℝ)/4) * (2*(n:ℝ)^2*y-3) *
             Real.exp (-(n:ℝ)^2*y)| ≤
        (n:ℝ)^2 *
          ((5*(n:ℝ)^2*Real.exp (-(n:ℝ)^2*y0/2)) *
            (y ^ (2:ℝ)*Real.exp (-y/2))) :=
        mul_le_mul_of_nonneg_left h hp0
      _ = (5*(n:ℝ)^4*Real.exp (-(n:ℝ)^2*y0/2)) *
            (y ^ (2:ℝ)*Real.exp (-y/2)) := by ring

theorem thetaYIntegrand_measurable (n : ℕ) :
    Measurable (thetaYIntegrand n) := by
  unfold thetaYIntegrand
  fun_prop

/-- Unconditional interchange for the exact y-integrand of the Riemann theta kernel. -/
theorem thetaY_integral_tsum (y0 : ℝ) (hy0 : 1 ≤ y0) :
    HasSum
      (fun n : ℕ => ∫ y in Set.Ici y0, thetaYIntegrand n y)
      (∫ y in Set.Ici y0, ∑' n : ℕ, thetaYIntegrand n y) := by
  let a : ℕ → ℝ :=
    fun n => 5*(n:ℝ)^4*Real.exp (-(n:ℝ)^2*y0/2)
  let b : ℝ → ℝ :=
    fun y => y ^ (2:ℝ)*Real.exp (-y/2)
  have hsA : Summable a :=
    theta_gaussian_weight_summable y0 (by linarith)
  have hB : Integrable b (volume.restrict (Set.Ici y0)) :=
    theta_y_weight_integrableOn y0 (by linarith)
  have hmeas : ∀ n : ℕ,
      AEStronglyMeasurable (thetaYIntegrand n)
        (volume.restrict (Set.Ici y0)) := by
    intro n
    exact (thetaYIntegrand_measurable n).aestronglyMeasurable
  have hbd : ∀ᵐ y ∂(volume.restrict (Set.Ici y0)),
      ∀ n : ℕ, ‖thetaYIntegrand n y‖ ≤ a n*b y := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with y hy n
    rw [Real.norm_eq_abs]
    exact thetaYIntegrand_bound n y y0 hy0 hy
  exact hasSum_integral_of_separable_bound
    (volume.restrict (Set.Ici y0)) thetaYIntegrand a b hsA hB hmeas hbd

end W5
