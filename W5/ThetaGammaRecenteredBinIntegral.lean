import W5.ThetaGammaRecenteredFourthRoot
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# One integration theorem for all recentered Gamma w-bins

The locally recentered quadratic-lower and cubic-upper fourth-root
envelopes from #156 are CONTINUOUS in w and multiply the nonnegative
real Gamma density exp(-w)*w^k on every w>=0. Consequently the exact
Mathlib interval-integral monotonicity theorem transports both
pointwise inequalities to a genuine weighted-moment interval.

Only the finite polynomial integrals and a uniform remaining w-tail
must be evaluated numerically by exact rational certified endpoints.
This is a single theorem for every k,q,L,U, not 48 cell proofs.
-/

namespace W5

/-- Original real fourth-root theta weight, no approximation. -/
noncomputable def thetaGammaBinOriginalRoot (q w : ℝ) : ℝ :=
  (1+q*w)^((1:ℝ)/4)

/-- Recentered quadratic lower fourth-root polynomial. -/
noncomputable def thetaGammaBinLowerRoot (q L w : ℝ) : ℝ :=
  let A := thetaGammaBinBase q L
  let v := thetaGammaBinOffset q L w
  A^((1:ℝ)/4)*(1+v/4-3*v^2/32)

/-- Recentered cubic upper fourth-root polynomial. -/
noncomputable def thetaGammaBinUpperRoot (q L w : ℝ) : ℝ :=
  let A := thetaGammaBinBase q L
  let v := thetaGammaBinOffset q L w
  A^((1:ℝ)/4)*(1+v/4-3*v^2/32+7*v^3/128)

/-- One nonnegative Gamma density, for any moment index k. -/
noncomputable def thetaGammaBinDensity (k : ℕ) (w : ℝ) : ℝ :=
  Real.exp (-w)*w^k

/-- Global continuity in the integration variable w; all divisions
are by a CONSTANT base A=1+qL and require no variable-domain
admissibility assumptions. -/
theorem thetaGammaBinLowerRoot_continuous
    (q L : ℝ) :
    Continuous (thetaGammaBinLowerRoot q L) := by
  unfold thetaGammaBinLowerRoot thetaGammaBinOffset
  simp only [div_eq_mul_inv]
  fun_prop

theorem thetaGammaBinUpperRoot_continuous
    (q L : ℝ) :
    Continuous (thetaGammaBinUpperRoot q L) := by
  unfold thetaGammaBinUpperRoot thetaGammaBinOffset
  simp only [div_eq_mul_inv]
  fun_prop

theorem thetaGammaBinOriginalRoot_continuous
    (q : ℝ) :
    Continuous (thetaGammaBinOriginalRoot q) := by
  unfold thetaGammaBinOriginalRoot
  exact (Real.continuous_rpow_const (by norm_num)).comp
    (by fun_prop : Continuous (fun w : ℝ => 1+q*w))

theorem thetaGammaBinDensity_continuous
    (k : ℕ) :
    Continuous (thetaGammaBinDensity k) := by
  unfold thetaGammaBinDensity
  fun_prop

/-- One nonnegative-weighted lower and upper bound for EVERY
original weighted Gamma moment on a finite integration bin.
The only original analytic input is the fourth-root inequalities,
and the only integration input is Mathlib intervalIntegral.mono. -/
theorem thetaGammaBinWeightedIntegral_bounds
    (q L U : ℝ) (k : ℕ)
    (hq : 0 ≤ q) (hL : 0 ≤ L) (hLU : L ≤ U) :
    (∫ w in L..U,
       thetaGammaBinDensity k w *
         thetaGammaBinLowerRoot q L w) ≤
      (∫ w in L..U,
       thetaGammaBinDensity k w *
         thetaGammaBinOriginalRoot q w) ∧
    (∫ w in L..U,
       thetaGammaBinDensity k w *
         thetaGammaBinOriginalRoot q w) ≤
      (∫ w in L..U,
       thetaGammaBinDensity k w *
         thetaGammaBinUpperRoot q L w) := by
  have hD : Continuous (thetaGammaBinDensity k) :=
    thetaGammaBinDensity_continuous k
  have hLow : Continuous (fun w : ℝ =>
      thetaGammaBinDensity k w *
        thetaGammaBinLowerRoot q L w) :=
    hD.mul (thetaGammaBinLowerRoot_continuous q L)
  have hMid : Continuous (fun w : ℝ =>
      thetaGammaBinDensity k w *
        thetaGammaBinOriginalRoot q w) :=
    hD.mul (thetaGammaBinOriginalRoot_continuous q)
  have hUp : Continuous (fun w : ℝ =>
      thetaGammaBinDensity k w *
        thetaGammaBinUpperRoot q L w) :=
    hD.mul (thetaGammaBinUpperRoot_continuous q L)
  have hbound (w : ℝ) (hw : w ∈ Set.Icc L U) :
      thetaGammaBinDensity k w *
        thetaGammaBinLowerRoot q L w ≤
      thetaGammaBinDensity k w *
        thetaGammaBinOriginalRoot q w ∧
      thetaGammaBinDensity k w *
        thetaGammaBinOriginalRoot q w ≤
      thetaGammaBinDensity k w *
        thetaGammaBinUpperRoot q L w := by
    have hw0 : 0 ≤ w := hL.trans hw.1
    have hnonneg :
        0 ≤ thetaGammaBinDensity k w :=
      mul_nonneg (Real.exp_nonneg _) (pow_nonneg hw0 k)
    have hRoot :=
      thetaGammaBinFourthRoot_recentered_bounds q L w hq hL hw.1
    change thetaGammaBinLowerRoot q L w ≤
        thetaGammaBinOriginalRoot q w ∧
      thetaGammaBinOriginalRoot q w ≤
        thetaGammaBinUpperRoot q L w at hRoot
    exact ⟨
      mul_le_mul_of_nonneg_left hRoot.1 hnonneg,
      mul_le_mul_of_nonneg_left hRoot.2 hnonneg⟩
  exact ⟨
    intervalIntegral.integral_mono_on hLU
      (hLow.intervalIntegrable L U)
      (hMid.intervalIntegrable L U)
      (fun w hw => (hbound w hw).1),
    intervalIntegral.integral_mono_on hLU
      (hMid.intervalIntegrable L U)
      (hUp.intervalIntegrable L U)
      (fun w hw => (hbound w hw).2)⟩

end W5
