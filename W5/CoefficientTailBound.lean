import W5.AnalyticTargets

/-!
# Explicit upper bound for the 25 theta coefficient polynomials

A direct finite proof attempt for all i,j∈Fin 5 and d,q≥0:
  |B_ij(d,q)| ≤ 5 (1+d)^8 (1+q)^4.

No theorem is assumed from the interval program. This estimate
is a necessary ingredient for the omitted-square-series tail.
It does not by itself prove the entire analytic theta remainder.
-/

namespace W5

theorem coefficientPolynomial_abs_bound
    (i j : Fin 5) (d q : ℝ) (hd : 0 ≤ d) (hq : 0 ≤ q) :
    |coefficientPolynomial i j d q| ≤
      (5:ℝ) * (1+d)^8 * (1+q)^4 := by
  apply abs_le.mpr
  constructor
  · have hp : 0 ≤ (5:ℝ) * (1+d)^8 * (1+q)^4 +
        coefficientPolynomial i j d q := by
      fin_cases i <;> fin_cases j <;>
        norm_num [coefficientPolynomial, Finset.sum_range_succ] <;>
        ring_nf <;> (first | positivity | trace_state)
    linarith
  · have hp : 0 ≤ (5:ℝ) * (1+d)^8 * (1+q)^4 -
        coefficientPolynomial i j d q := by
      fin_cases i <;> fin_cases j <;>
        norm_num [coefficientPolynomial, Finset.sum_range_succ] <;>
        ring_nf <;> (first | positivity | trace_state)
    linarith

end W5
