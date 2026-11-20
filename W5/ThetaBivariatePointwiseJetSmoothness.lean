import W5.ThetaTwoVariableSummableJetEnvelopes

/-!
# Simultaneous C-infinity regularity of the exact weighted theta integrands

The local two-variable Mathlib smooth-series lemma (PR #78)
requires a genuine Fréchet derivative of each n-th integrated
term. Before passing this derivative through the unbounded
Lebesgue integral, we verify that the ACTUAL pointwise
weighted theta Gaussian and its arbitrary-order higher right
and mixed jets are C-infinity functions of the two Taylor
coordinates simultaneously, not just separately C-infinity.

This is true for ALL fixed x,p,d0,w,n, with the artificial n=0
convention treated directly. The quarter-power w-weight does
not involve u or v, so its differentiability is irrelevant;
as a parameter-independent constant, even a singular p=0
is harmless to the pointwise parameter smoothness.

These statements close the smoothness part of Mathlib's
two-variable derivative-under-integral argument. The remaining
work is the uniform local integral majorant of its Fréchet
derivative, which will be supplied from the already proved
Gaussian first-jet envelopes, not assumed.
-/

namespace W5

/-- The genuine weighted Gaussian integrand is C-infinity
simultaneously in the two Taylor parameters. -/
theorem thetaWeightedGaussianIntegrand_contDiff_twoVariable
    (x p d0 w : ℝ) :
    ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaWeightedGaussianIntegrand x p d0 (z 0) (z 1) w) := by
  unfold thetaWeightedGaussianIntegrand thetaGaussianModel
  fun_prop

/-- Every kth right jet of the genuine weighted Gaussian
is C-infinity in both variables. This includes its actual
u-dependent affine kth-jet multiplier. -/
theorem thetaWeightedGaussianRightJet_contDiff_twoVariable
    (k : ℕ) (x p d0 w : ℝ) :
    ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaWeightedGaussianRightJet k x p d0 (z 0) (z 1) w) := by
  unfold thetaWeightedGaussianRightJet
    thetaWeightedGaussianRightMultiplier
    thetaWeightedGaussianIntegrand thetaGaussianModel
  fun_prop

/-- After the n² substitution and the exterior theta damping,
the actual kth RIGHT jet at index n is C-infinity jointly
in both Taylor parameters. The square index n=0 vanishes. -/
theorem thetaHigherRightJetSeriesTerm_contDiff_twoVariable
    (k : ℕ) (x : ℝ) (n : ℕ) (w : ℝ) :
    ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaHigherRightJetSeriesTerm k x (z 0) (z 1) n w) := by
  by_cases hn : n = 0
  · subst n
    change ContDiff ℝ ⊤ (fun _ : Fin 2 → ℝ => (0:ℝ))
    exact contDiff_const
  · have h := (thetaWeightedGaussianRightJet_contDiff_twoVariable
      k x ((n:ℝ)^2) (((n:ℝ)^2-1)/x) w).const_mul
      (Real.exp (-((n:ℝ)^2-1)/x^2))
    change ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        if n = 0 then (0:ℝ) else
          Real.exp (-((n:ℝ)^2-1)/x^2) *
            thetaWeightedGaussianRightJet k x ((n:ℝ)^2)
              (((n:ℝ)^2-1)/x) (z 0) (z 1) w)
    simpa only [if_neg hn] using h

/-- Every kth LEFT theta jet is C-infinity jointly in (u,v)
by transporting the result for right jets under coordinate
exchange. This holds at all n, including n=0. -/
theorem thetaHigherLeftJetSeriesTerm_contDiff_twoVariable
    (k : ℕ) (x : ℝ) (n : ℕ) (w : ℝ) :
    ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaHigherLeftJetSeriesTerm k x (z 0) (z 1) n w) := by
  by_cases hn : n = 0
  · subst n
    change ContDiff ℝ ⊤ (fun _ : Fin 2 → ℝ => (0:ℝ))
    exact contDiff_const
  · change ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaHigherRightJetSeriesTerm k x (z 1) (z 0) n w)
    have h := thetaHigherRightJetSeriesTerm_contDiff_twoVariable k x n w
    have hswap : ContDiff ℝ ⊤
        (fun z : Fin 2 → ℝ => (fun i : Fin 2 =>
          if i = 0 then z 1 else z 0)) := by
      fun_prop
    convert h.comp hswap using 1
    funext z
    simp

/-- The ACTUAL mixed jet (one left and k right) of each
weighted theta term is also C-infinity in both Taylor variables.
This is the joint-smoothness prerequisite for third- through
eighth-order mixed derivative interchanges. -/
theorem thetaMixedOneRightJetSeriesTerm_contDiff_twoVariable
    (k : ℕ) (x : ℝ) (n : ℕ) (w : ℝ) :
    ContDiff ℝ ⊤
      (fun z : Fin 2 → ℝ =>
        thetaMixedOneRightJetSeriesTerm k x (z 0) (z 1) n w) := by
  by_cases hn : n = 0
  · subst n
    change ContDiff ℝ ⊤ (fun _ : Fin 2 → ℝ => (0:ℝ))
    exact contDiff_const
  · simp only [thetaMixedOneRightJetSeriesTerm, if_neg hn]
    dsimp [thetaWeightedGaussianRightMultiplier,
      thetaWeightedGaussianIntegrand, thetaGaussianModel]
    fun_prop

end W5
