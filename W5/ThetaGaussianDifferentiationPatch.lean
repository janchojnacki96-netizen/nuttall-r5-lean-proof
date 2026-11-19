import W5.ThetaWeightedGaussianDerivative
import Mathlib.Topology.Algebra.Order.Field

/-!
# A shared neighborhood for differentiating the theta w-integrand

The Mathlib parametric-integral derivative theorem requires an open
neighborhood of the evaluation point and a single derivative majorant
on that whole neighborhood. The existing bound is valid whenever
|v| ≤ 1 and x*v ≥ -1/2. We exhibit an open neighborhood of v=0
strictly inside those constraints, for every fixed real x.

This is a local topological fact, not yet a differentiation-under-integral
or term-by-term theta-series theorem.
-/

namespace W5

/-- An explicit open patch around the origin used when treating v
as the differentiation parameter of one weighted theta w-integral. -/
def thetaGaussianRightPatch (x : ℝ) : Set ℝ :=
  {z : ℝ | |z| < 1 ∧ -(1:ℝ)/2 < x*z}

/-- The patch is open because it is the intersection of strict
inequalities between continuous real-valued functions. -/
theorem thetaGaussianRightPatch_isOpen (x : ℝ) :
    IsOpen (thetaGaussianRightPatch x) := by
  change IsOpen
    ({z : ℝ | |z| < 1} ∩ {z : ℝ | -(1:ℝ)/2 < x*z})
  exact (isOpen_lt continuous_abs continuous_const).inter
    (isOpen_lt continuous_const
      (continuous_const.mul continuous_id))

/-- The same explicit patch is a genuine neighborhood of zero,
without any assumption on x. -/
theorem thetaGaussianRightPatch_mem_nhds (x : ℝ) :
    thetaGaussianRightPatch x ∈ nhds (0:ℝ) := by
  apply (thetaGaussianRightPatch_isOpen x).mem_nhds
  change |(0:ℝ)| < 1 ∧ -(1:ℝ)/2 < x*0
  constructor <;> norm_num

/-- Every point in this open neighborhood satisfies precisely the
non-strict inequalities needed by the uniform Gaussian envelope. -/
theorem thetaGaussianRightPatch_bounds (x z : ℝ)
    (hz : z ∈ thetaGaussianRightPatch x) :
    |z| ≤ 1 ∧ -(1:ℝ)/2 ≤ x*z := by
  exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩

end W5
