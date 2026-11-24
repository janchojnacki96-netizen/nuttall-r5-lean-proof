import W5.AnalyticTargets
import W5.BoundaryPivots

/-!
Exact evaluation of the limiting polynomial B_ij(d,q) at d=0,q=1,
which is the n=1 zero-coordinate model in the theta certificate.

This does not assert that the complete analytic theta kernel has a
proven limiting value in Lean.
-/
namespace W5

theorem coefficientPolynomial_at_zero_one (i j : Fin 5) :
    coefficientPolynomial i j 0 1 =
      if i = j then boundaryPivot i else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [coefficientPolynomial, boundaryPivot, Finset.sum_range_succ]

end W5
