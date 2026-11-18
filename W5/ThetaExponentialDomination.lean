import W5.ThetaGaussianSummability
import W5.ThetaTermIntegrability

/-!
# Decoupling the theta Gaussian decay

For p>=1 and y>=y0>=0,
    exp(-p*y) <= exp(-p*y0/2) * exp(-y/2).
This separates the index-dependent Gaussian factor from an integrable
function of the integration variable. It is a key pointwise estimate
towards proving a valid exchange between the theta n-sum and the
improper y-integral; the Fubini / dominated-convergence step itself
is not yet claimed here.
-/

namespace W5

theorem theta_exp_split_bound (p y y0 : ℝ)
    (hp : 1 ≤ p) (hy0 : 0 ≤ y0) (hy : y0 ≤ y) :
    Real.exp (-p*y) ≤
      Real.exp (-p*y0/2) * Real.exp (-y/2) := by
  have hp0 : 0 ≤ p := by linarith
  have hypos : 0 ≤ y := le_trans hy0 hy
  have h1 : p*y0 ≤ p*y :=
    mul_le_mul_of_nonneg_left hy hp0
  have h2 : y ≤ p*y := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hypos
  calc
    Real.exp (-p*y) ≤ Real.exp (-p*y0/2 + -y/2) :=
      Real.exp_le_exp.mpr (by nlinarith [h1, h2])
    _ = Real.exp (-p*y0/2) * Real.exp (-y/2) := by
      rw [Real.exp_add]

theorem theta_square_index_exp_split_bound (n : ℕ)
    (hn : 1 ≤ n) (y y0 : ℝ)
    (hy0 : 0 ≤ y0) (hy : y0 ≤ y) :
    Real.exp (-(n:ℝ)^2*y) ≤
      Real.exp (-(n:ℝ)^2*y0/2) * Real.exp (-y/2) := by
  have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hp : (1:ℝ) ≤ (n:ℝ)^2 := by
    nlinarith [sq_nonneg ((n:ℝ)-1)]
  exact theta_exp_split_bound ((n:ℝ)^2) y y0 hp hy0 hy

end W5
