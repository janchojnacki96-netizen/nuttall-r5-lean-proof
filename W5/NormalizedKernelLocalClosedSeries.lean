import W5.ThetaClosedFormLocalExtension
import W5.NormalizedKernelZeroth

/-!
# Exact local theta series for the genuinely normalized kernel

The original normalizedKernel contains the actual Psi1. The
noncomputable closed-series expression below is written by replacing
Psi1 with its previously established, exact closed theta series.

For x=xOfT(t) with t>=0, the two kernels agree on an explicit
two-variable neighborhood of u=v=0. This includes t=0 and does NOT
assume that either shifted time is nonnegative.

Equality of functions locally is not a proof of the interchange
of derivatives with the countable theta series/integrals.
-/

namespace W5

/-- The explicit closed-theta-series surrogate for the original
normalized kernel. It is not used as an assumption. -/
noncomputable def normalizedThetaClosedKernel (x u v : ℝ) : ℝ :=
  let y : ℝ := 1 / x ^ (2 : ℕ)
  let t : ℝ := Real.log (y / Real.pi) / 4
  let su : ℝ := Real.log (1 + x*u) / 4
  let sv : ℝ := Real.log (1 + x*v) / 4
  (2 * Real.pi ^ ((1 : ℝ)/4) * Real.exp y / y ^ ((5 : ℝ)/4)) *
    (Real.exp (u/x) * Real.exp (v/x) /
      ((1+x*u) ^ ((5 : ℝ)/4) * (1+x*v) ^ ((5 : ℝ)/4))) *
    psiThetaClosedSeries (t + su + sv)

/-- The original normalized kernel and its exact closed series
agree pointwise on a two-variable neighborhood of each t>=0. -/
theorem normalizedKernel_eq_closed_theta_on_local_patch
    (t u v : ℝ) (ht : 0 ≤ t)
    (hu : -(1:ℝ)/4 ≤ (xOfT t)*u)
    (hv : -(1:ℝ)/4 ≤ (xOfT t)*v) :
    normalizedKernel (xOfT t) u v =
      normalizedThetaClosedKernel (xOfT t) u v := by
  have hpsi :
      Psi1 (thetaTimeOfX (xOfT t) +
          Real.log (1+(xOfT t)*u)/4 +
          Real.log (1+(xOfT t)*v)/4) =
        psiThetaClosedSeries
          (thetaTimeOfX (xOfT t) +
            Real.log (1+(xOfT t)*u)/4 +
            Real.log (1+(xOfT t)*v)/4) := by
    rw [thetaTimeOfX_xOfT]
    exact Psi1_eq_closed_theta_series_on_local_patch
      t (xOfT t) u v ht hu hv
  unfold normalizedKernel normalizedThetaClosedKernel
  dsimp only
  simpa only [thetaTimeOfX] using
    congrArg
      (fun z : ℝ =>
        (2 * Real.pi ^ ((1:ℝ)/4) *
          Real.exp (1/(xOfT t)^2) /
          (1/(xOfT t)^2) ^ ((5:ℝ)/4)) *
        (Real.exp (u/(xOfT t)) * Real.exp (v/(xOfT t)) /
          ((1+(xOfT t)*u)^((5:ℝ)/4) *
            (1+(xOfT t)*v)^((5:ℝ)/4))) * z)
      hpsi

end W5
