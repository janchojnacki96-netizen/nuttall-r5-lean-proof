import W5.PsiFundamentalDerivative
import W5.ThetaIntegralStrictPositivity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Strict decrease of the genuine theta tail on the nonnegative half-line

This strengthens the previously proved W1 > 0 with a global shape
property, using the exact fundamental derivative Psi1' = -Phi and
strict positivity of the original theta kernel for t >= 0.

It does NOT imply the W2 log-curvature sign; that remains open.
-/

namespace W5

/-- Strictly negative first derivative of the ORIGINAL Psi1 on t >= 0. -/
theorem Psi1_deriv_neg (t : ℝ) (ht : 0 ≤ t) :
    deriv Psi1 t < 0 := by
  rw [Psi1_deriv]
  exact neg_neg.mpr (Phi_pos t ht)

/-- The actual original theta tail is strictly decreasing on [0,∞). -/
theorem Psi1_strictAntiOn_nonneg :
    StrictAntiOn Psi1 (Set.Ici (0:ℝ)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici)
  · exact (fun t => (Psi1_hasDerivAt t).continuousAt).continuous.continuousOn
  · intro t ht
    exact Psi1_deriv_neg t (by
      have h : t ∈ Set.Ici (0:ℝ) := interior_subset ht
      exact h)

/-- For nonnegative t < u, the positive W1 value strictly decreases. -/
theorem W_one_strict_decrease (t u : ℝ)
    (ht : 0 ≤ t) (htu : t < u) :
    W 1 u < W 1 t := by
  rw [W_one_eq_Psi1, W_one_eq_Psi1]
  exact Psi1_strictAntiOn_nonneg ht (le_of_lt (lt_of_le_of_lt ht htu)) htu

/-- The first Wronskian remains strictly positive while decreasing. -/
theorem W_one_pos_and_decreases (t u : ℝ)
    (ht : 0 ≤ t) (htu : t < u) :
    0 < W 1 u ∧ W 1 u < W 1 t := by
  exact ⟨W_one_pos u (le_trans ht htu.le),
    W_one_strict_decrease t u ht htu⟩

end W5
