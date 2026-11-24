import W5.ThetaGaussianIntegratedDerivativeBound
import Mathlib.Topology.Order.IntermediateValue

/-!
# A connected open theta parameter patch with summable derivative bounds

The generic theorem `hasDerivAt_tsum_of_isPreconnected` from Mathlib
requires a *common connected open neighborhood* of the evaluation
point, differentiability of every term there, and a summable bound
independent of the varying parameter.

The older thetaGaussianRightPatch x is sufficient for differentiating
a fixed index, but its large radius cannot preserve Gaussian
summability over n. We therefore use the smaller open interval
(-x/8, x/8) and show it lies inside the older differentiability
patch while retaining the uniform Gaussian estimate.

No interchange of an entire derivative with the theta n-sum is
asserted in this module. Convergence of the undifferentiated
integrated terms at a basepoint remains a separate obligation.
-/

namespace W5
open MeasureTheory

/-- The open, connected theta parameter neighborhood whose radius
scales with the small theta variable x. -/
def thetaGaussianSummableRightPatch (x : ℝ) : Set ℝ :=
  Set.Ioo (-x/8) (x/8)

theorem thetaGaussianSummableRightPatch_isOpen (x : ℝ) :
    IsOpen (thetaGaussianSummableRightPatch x) := by
  exact isOpen_Ioo

theorem thetaGaussianSummableRightPatch_isPreconnected (x : ℝ) :
    IsPreconnected (thetaGaussianSummableRightPatch x) := by
  exact isPreconnected_Ioo

theorem thetaGaussianSummableRightPatch_zero_mem
    (x : ℝ) (hx : 0 < x) :
    (0:ℝ) ∈ thetaGaussianSummableRightPatch x := by
  change -x/8 < (0:ℝ) ∧ (0:ℝ) < x/8
  have hx8 : 0 < x/8 := by positivity
  constructor
  · linarith [hx8]
  · exact hx8

/-- Members of the open patch lie in the closed small box needed
by the Gaussian n-index estimates. -/
theorem thetaGaussianSummableRightPatch_abs_le
    (x v : ℝ) (hv : v ∈ thetaGaussianSummableRightPatch x) :
    |v| ≤ x/8 := by
  change -x/8 < v ∧ v < x/8 at hv
  apply abs_le.mpr
  constructor <;> linarith [hv.1, hv.2]

/-- The summability patch lies inside the larger Gaussian
differentiability patch for every 0<x<=1. -/
theorem thetaGaussianSummableRightPatch_subset_rightPatch
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1) :
    thetaGaussianSummableRightPatch x ⊆ thetaGaussianRightPatch x := by
  intro v hv
  change -x/8 < v ∧ v < x/8 at hv
  have hvabs : |v| < x/8 := by
    apply abs_lt.mpr
    constructor <;> linarith [hv.1, hv.2]
  have hsmall : |v| < 1 := by linarith
  have hprod : 0 < x*(v+x/8) :=
    mul_pos hx (by linarith [hv.1])
  have hx2 : x^2 ≤ 1 := by
    nlinarith [mul_nonneg hx.le (by linarith : 0 ≤ 1-x)]
  change |v| < 1 ∧ -(1:ℝ)/2 < x*v
  constructor
  · exact hsmall
  · nlinarith [hprod, hx2]

/-- The norm of the derivative of each integrated theta term admits
the same index-summable bound everywhere on the common open patch. -/
theorem thetaGaussian_nonzero_index_integrated_deriv_bound_on_summablePatch
    (x : ℝ) (hx : 0 < x) (hx1 : x ≤ 1)
    (n : ℕ) (hn : 1 ≤ n)
    (u v : ℝ) (hu : |u| ≤ x/8)
    (hv : v ∈ thetaGaussianSummableRightPatch x) :
    ‖Real.exp (-((n:ℝ)^2-1)/x^2) *
      (∫ w : ℝ,
        thetaWeightedGaussianRightDerivative x ((n:ℝ)^2)
          (((n:ℝ)^2-1)/x) u v w
        ∂(volume.restrict (Set.Ioi (0:ℝ))))‖ ≤
      (Real.exp (3/4)*(1/x+2)) *
        (∫ w : ℝ, thetaGaussianProductMajorant n w
          ∂(volume.restrict (Set.Ioi (0:ℝ)))) := by
  exact thetaGaussian_nonzero_index_integrated_deriv_norm_le
    x hx hx1 n hn u v hu
      (thetaGaussianSummableRightPatch_abs_le x v hv)

/-- The parameter-independent right-hand side above is genuinely
summable as a sequence of real numbers. -/
theorem thetaGaussian_integrated_deriv_majorant_summable
    (x : ℝ) :
    Summable (fun n : ℕ =>
      (Real.exp (3/4)*(1/x+2)) *
        (∫ w : ℝ, thetaGaussianProductMajorant n w
          ∂(volume.restrict (Set.Ioi (0:ℝ))))) := by
  exact thetaGaussianProductMajorant_integrals_summable.mul_left
    (Real.exp (3/4)*(1/x+2))

end W5
