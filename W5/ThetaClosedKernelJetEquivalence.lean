import W5.NormalizedKernelLocalClosedSeries
import W5.NormalizedKernelSymmetry

/-!
# From local equality of the ORIGINAL kernel to equality of its jets

PR #17 proved that the genuine normalized Psi1 kernel and the exact
closed theta-series kernel agree on a two-variable neighborhood
around u=v=0, including at t=0. As a result, their first and mixed
derivatives at the origin agree by locality of differentiation.

This module proves those jet identities unconditionally via
Filter.EventuallyEq.deriv_eq. Crucially, it does NOT differentiate
under a theta integral or a countable sum. That analytic operation
remains to be justified separately for the closed-series kernel.
-/

namespace W5

/-- For any real x the condition x*v >= -1/4 holds eventually near v=0. -/
private theorem eventually_mul_ge_quarter (x : ℝ) :
    ∀ᶠ v : ℝ in 𝓝 (0:ℝ), -(1:ℝ)/4 ≤ x*v := by
  have hcont : ContinuousAt (fun v : ℝ => x*v) (0:ℝ) := by
    fun_prop
  have hnhds :
      Set.Ioi (-(1:ℝ)/4) ∈ 𝓝 (0:ℝ) :=
    Ioi_mem_nhds (by norm_num)
  have hnear := hcont.tendsto.eventually hnhds
  filter_upwards [hnear] with v hv
  exact le_of_lt hv

/-- Equality of the genuine first Taylor derivative and the derivative
of the closed theta-series kernel, without any differentiation under
the integral or the infinite sum. -/
theorem normalizedKernel_right_deriv_eq_closed_theta
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (fun v : ℝ => normalizedKernel (xOfT t) 0 v) 0 =
      deriv (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) 0 v) 0 := by
  have hlocal :
      (fun v : ℝ => normalizedKernel (xOfT t) 0 v) =ᶠ[𝓝 (0:ℝ)]
      (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) 0 v) := by
    filter_upwards [eventually_mul_ge_quarter (xOfT t)] with v hv
    exact normalizedKernel_eq_closed_theta_on_local_patch
      t 0 v ht (by norm_num) hv
  exact hlocal.deriv_eq

/-- The original (0,1) coefficient is an actual derivative of the
closed theta kernel. This equality is unconditional on the ray. -/
theorem analyticCoeff_zero_one_eq_closed_theta_deriv
    (t : ℝ) (ht : 0 ≤ t) :
    analyticCoeff (xOfT t) (0 : Fin 5) (1 : Fin 5) =
      deriv (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) 0 v) 0 := by
  rw [analyticCoeff_zero_one_deriv]
  exact normalizedKernel_right_deriv_eq_closed_theta t ht

/-- Equality of the ORIGINAL (1,1) mixed derivative and that of the
closed theta-series kernel, obtained by applying derivative locality
twice. No analyticity or differentiability-under-sum premise is used. -/
theorem normalizedKernel_mixed_deriv_eq_closed_theta
    (t : ℝ) (ht : 0 ≤ t) :
    deriv (fun u : ℝ =>
      deriv (fun v : ℝ => normalizedKernel (xOfT t) u v) 0) 0 =
    deriv (fun u : ℝ =>
      deriv (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) 0) 0 := by
  have hnear_u := eventually_mul_ge_quarter (xOfT t)
  have hnear_v := eventually_mul_ge_quarter (xOfT t)
  have houter :
      (fun u : ℝ =>
        deriv (fun v : ℝ => normalizedKernel (xOfT t) u v) 0) =ᶠ[𝓝 (0:ℝ)]
      (fun u : ℝ =>
        deriv (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) 0) := by
    filter_upwards [hnear_u] with u hu
    have hinner :
        (fun v : ℝ => normalizedKernel (xOfT t) u v) =ᶠ[𝓝 (0:ℝ)]
        (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) := by
      filter_upwards [hnear_v] with v hv
      exact normalizedKernel_eq_closed_theta_on_local_patch
        t u v ht hu hv
    exact hinner.deriv_eq
  exact houter.deriv_eq

/-- The actual normalized analytic Taylor coefficient A11 agrees
with the mixed ordinary derivative of the exact closed theta
series kernel, reducing the remaining coefficient-identification
problem to rigorous differentiation of that closed series/integral. -/
theorem analyticCoeff_one_one_eq_closed_theta_mixed_deriv
    (t : ℝ) (ht : 0 ≤ t) :
    analyticCoeff (xOfT t) (1 : Fin 5) (1 : Fin 5) =
      deriv (fun u : ℝ =>
        deriv (fun v : ℝ =>
          normalizedThetaClosedKernel (xOfT t) u v) 0) 0 := by
  simpa [analyticCoeff, iteratedDeriv_one] using
    (normalizedKernel_mixed_deriv_eq_closed_theta t ht)

end W5
