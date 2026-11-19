import W5.ThetaYFubini
import W5.ThetaSingleTermClosedForm

/-!
# Exact integrated theta series in the y-coordinate

This module joins two already-proved analytic ingredients:
* the genuine countable-series/integral interchange on [y₀, ∞);
* the single-square incomplete-gamma formula.

The result gives one exact closed-form series for the integrated
y-coordinate theta expression. It does NOT assert its identification
with the original t-coordinate `Psi1` until the Jacobian substitution
has separately been formalized.
-/

namespace W5

open MeasureTheory

/-- Each individual square-index integrand has an exact tail formula,
including the zero-index term (which vanishes). -/
theorem thetaYIntegrand_integral_closed_form (n : ℕ) (y₀ : ℝ)
    (hy₀ : 1 ≤ y₀) :
    (∫ y in Set.Ici y₀, thetaYIntegrand n y) =
      2 * (n : ℝ)^2 * y₀ ^ ((5 : ℝ)/4) *
        (Real.exp (-(n : ℝ)^2*y₀) -
          (1/4 : ℝ) *
            (∫ v in Set.Ioi (1 : ℝ),
               v ^ ((1 : ℝ)/4) *
                 Real.exp (-(n : ℝ)^2*y₀*v))) := by
  by_cases hn : n = 0
  · subst n
    simp [thetaYIntegrand]
  · have hp : 0 < (n : ℝ)^2 := by
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      positivity
    have hypos : 0 < y₀ := lt_of_lt_of_le (by norm_num) hy₀
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    change (∫ y in Set.Ioi y₀,
        (n : ℝ)^2 *
          (y ^ ((1 : ℝ)/4) * (2 * (n : ℝ)^2*y - 3) *
            Real.exp (-(n : ℝ)^2*y))) = _
    rw [MeasureTheory.integral_const_mul]
    rw [theta_single_square_closed_form ((n : ℝ)^2) y₀ hp hypos]
    ring

/-- Exact infinite-series closed form for the integrated theta y-kernel.
No numeric certificate and no extra analytical assumptions are used. -/
theorem thetaY_integral_tsum_closed_form (y₀ : ℝ) (hy₀ : 1 ≤ y₀) :
    (∫ y in Set.Ici y₀, ∑' n : ℕ, thetaYIntegrand n y) =
      ∑' n : ℕ,
        2 * (n : ℝ)^2 * y₀ ^ ((5 : ℝ)/4) *
          (Real.exp (-(n : ℝ)^2*y₀) -
            (1/4 : ℝ) *
              (∫ v in Set.Ioi (1 : ℝ),
                v ^ ((1 : ℝ)/4) *
                  Real.exp (-(n : ℝ)^2*y₀*v))) := by
  calc
    (∫ y in Set.Ici y₀, ∑' n : ℕ, thetaYIntegrand n y) =
        ∑' n : ℕ, ∫ y in Set.Ici y₀, thetaYIntegrand n y :=
          (thetaY_integral_tsum y₀ hy₀).tsum_eq.symm
    _ = _ := by
      congr 1
      funext n
      exact thetaYIntegrand_integral_closed_form n y₀ hy₀

end W5
