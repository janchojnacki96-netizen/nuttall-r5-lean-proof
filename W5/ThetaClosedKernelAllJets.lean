import W5.ThetaClosedKernelJetEquivalence
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# All 25 genuine normalized Taylor jets agree with the closed theta series

A local equality of two functions carries ALL their iterated ordinary
derivatives, regardless of differentiability assumptions: iteratedDeriv
is local. We apply this principle separately in the inner v-variable
and outer u-variable.

Consequently the original analytic coefficients with i,j <= 4
are exactly the corresponding derivatives of the independently
defined, but PROVEN locally equal, closed theta series kernel.

This is not an identification with the numerical `thetaCoefficient`:
interchanging derivatives with the improper integral and infinite sum
is a further (currently unproved) theorem.
-/

namespace W5

/-- A fixed local neighborhood of zero keeps the normalized theta
coordinate within the domain of the proven closed series. -/
private theorem allJets_eventually_mul_ge_quarter (x : ℝ) :
    ∀ᶠ v : ℝ in 𝓝 (0:ℝ), -(1:ℝ)/4 ≤ x*v := by
  have hc : ContinuousAt (fun v : ℝ => x*v) 0 := by
    fun_prop
  have hh : Set.Ioi (-(1:ℝ)/4) ∈ 𝓝 (0:ℝ) :=
    Ioi_mem_nhds (by norm_num)
  filter_upwards [hc.tendsto.eventually hh] with v hv
  exact le_of_lt hv

/-- Local equality transfers every order of differentiation in the
right coordinate for each sufficiently small fixed left coordinate. -/
theorem normalizedKernel_all_inner_jets_eventually_eq
    (t : ℝ) (ht : 0 ≤ t) (j : ℕ) :
    (fun u : ℝ =>
       iteratedDeriv j
         (fun v : ℝ => normalizedKernel (xOfT t) u v) 0) =ᶠ[𝓝 (0:ℝ)]
    (fun u : ℝ =>
       iteratedDeriv j
         (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) 0) := by
  filter_upwards [allJets_eventually_mul_ge_quarter (xOfT t)] with u hu
  have hv :
      (fun v : ℝ => normalizedKernel (xOfT t) u v) =ᶠ[𝓝 (0:ℝ)]
      (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) := by
    filter_upwards [allJets_eventually_mul_ge_quarter (xOfT t)] with v hv
    exact normalizedKernel_eq_closed_theta_on_local_patch t u v ht hu hv
  exact (hv.iteratedDeriv j).eq_of_nhds

/-- THE UNCONDITIONAL LOCAL JET BRIDGE, for all natural orders.
No Fubini theorem or derivative/summation interchange is used. -/
theorem normalizedKernel_all_mixed_jets_eq_closed
    (t : ℝ) (ht : 0 ≤ t) (i j : ℕ) :
    iteratedDeriv i
      (fun u : ℝ => iteratedDeriv j
        (fun v : ℝ => normalizedKernel (xOfT t) u v) 0) 0 =
    iteratedDeriv i
      (fun u : ℝ => iteratedDeriv j
        (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) 0) 0 := by
  have hlocal :=
    normalizedKernel_all_inner_jets_eventually_eq t ht j
  exact (hlocal.iteratedDeriv i).eq_of_nhds

/-- All 25 entries of the original 5-by-5 analytic Taylor matrix
agree exactly with the corresponding mixed derivatives of the
explicit closed theta series, on the full nonnegative t-ray. -/
theorem analyticCoeff_eq_closedThetaKernel_jet
    (t : ℝ) (ht : 0 ≤ t) (i j : Fin 5) :
    analyticCoeff (xOfT t) i j =
      (iteratedDeriv i.val
        (fun u : ℝ => iteratedDeriv j.val
          (fun v : ℝ => normalizedThetaClosedKernel (xOfT t) u v) 0) 0) /
      ((Nat.factorial i.val : ℝ) * (Nat.factorial j.val : ℝ)) := by
  have hjet := normalizedKernel_all_mixed_jets_eq_closed t ht i.val j.val
  unfold analyticCoeff
  exact congrArg (fun z : ℝ =>
    z / ((Nat.factorial i.val : ℝ) * (Nat.factorial j.val : ℝ))) hjet

end W5
