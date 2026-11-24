import W5.AnalyticTargets

/-!
# Exact symmetry of the theta coefficient matrix

The polynomial B_ij(d,q) appearing in the numerical theta
certificate is symmetric in i and j. Consequently its full
integral-and-infinite-sum theta coefficient matrix is symmetric
for every real x, WITHOUT any assumptions on approximation,
interval rounding, or the still unproved analytic Taylor bridge.

These identities alone do not establish matrix positivity or
any Wronskian determinant sign.
-/

namespace W5

theorem coefficientPolynomial_symmetric
    (i j : Fin 5) (d q : ℝ) :
    coefficientPolynomial i j d q =
      coefficientPolynomial j i d q := by
  unfold coefficientPolynomial
  have hmin : min i.val j.val + 1 = min j.val i.val + 1 := by
    rw [min_comm]
  rw [hmin]
  apply Finset.sum_congr rfl
  intro k hk
  have hsum : i.val + j.val = j.val + i.val := Nat.add_comm _ _
  rw [hsum]
  have hden :
      (Nat.factorial k : ℝ) *
          (Nat.factorial (i.val - k) : ℝ) *
          (Nat.factorial (j.val - k) : ℝ) =
        (Nat.factorial k : ℝ) *
          (Nat.factorial (j.val - k) : ℝ) *
          (Nat.factorial (i.val - k) : ℝ) := by
    ring
  rw [hden]

/-- The *actual* theta coefficient matrix used by the external
certificate is symmetric, including its infinite-series and
improper-integral terms, for every x. -/
theorem thetaCoefficient_symmetric
    (x : ℝ) (i j : Fin 5) :
    thetaCoefficient x i j = thetaCoefficient x j i := by
  unfold thetaCoefficient
  simp_rw [coefficientPolynomial_symmetric i j]

end W5
