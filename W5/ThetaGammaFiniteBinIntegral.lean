import W5.ThetaAuditedCorrectionMoment
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Universal exact finite-bin Gamma integral

For all nonnegative integer k and any real endpoints L,U,
  ∫_L^U exp(-w) * w^k dw
    = exp(-L) * P_k(L) - exp(-U) * P_k(U),

where the polynomial P_k has strictly nonnegative integer coefficients,
P_0=1 and P_{k+1}=(k+1)P_k+w^{k+1}.

Rather than reprove Gamma, use Mathlib's elementary HasDerivAt
derivative rules and intervalIntegral's second FTC, as in the
existing W5/ThetaFiniteBoundaryIntegral.lean.

This is the missing exact *finite-bin* algebra for a single
uniform theta weighted-moment quadrature. It works for all k,
all rational bins, all 48 x-cells, with no specialized cases.
The next step is certified exp(-L), exp(-U) and fourth-root
chord/tangent bounds (PR #153); this module alone doesn't claim
any numeric theta signs.
-/

namespace W5
open MeasureTheory intervalIntegral

/-- The truncated Gamma tail polynomial defined using a recurrence
that avoids factorial divisions and is executable over rationals. -/
def thetaGammaBinPolyQ : ℕ → ℚ → ℚ
  | 0, _ => 1
  | k+1, z => ((k+1:ℕ):ℚ) * thetaGammaBinPolyQ k z + z^(k+1)

/-- The same polynomial interpreted as a real function for
Mathlib's differentiation and fundamental theorem of calculus. -/
def thetaGammaBinPolyR : ℕ → ℝ → ℝ
  | 0, _ => 1
  | k+1, z => ((k+1:ℕ):ℝ) * thetaGammaBinPolyR k z + z^(k+1)

/-- Rational numerical polynomial evaluation EXACTLY agrees with
the real polynomial, so interval computations need no new casts. -/
theorem thetaGammaBinPolyQ_cast (k : ℕ) (z : ℚ) :
    (thetaGammaBinPolyQ k z : ℝ) =
      thetaGammaBinPolyR k (z:ℝ) := by
  induction k with
  | zero => simp [thetaGammaBinPolyQ, thetaGammaBinPolyR]
  | succ k ih =>
      simp only [thetaGammaBinPolyQ, thetaGammaBinPolyR,
        Rat.cast_add, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast]
      rw [ih]

/-- One all-orders polynomial derivative identity, obtained from
the recurrence and Mathlib's derivative of powers. -/
theorem thetaGammaBinPolyR_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt (thetaGammaBinPolyR k)
      (thetaGammaBinPolyR k x - x^k) x := by
  induction k with
  | zero =>
      convert (hasDerivAt_const x (1:ℝ)) using 1 <;>
        simp [thetaGammaBinPolyR]
  | succ k ih =>
      have hmul :
          HasDerivAt
            (fun y : ℝ => ((k+1:ℕ):ℝ) * thetaGammaBinPolyR k y)
            (((k+1:ℕ):ℝ) * (thetaGammaBinPolyR k x - x^k)) x :=
        (ih.const_mul ((k+1:ℕ):ℝ))
      have hpow :
          HasDerivAt (fun y : ℝ => y^(k+1))
            (((k+1:ℕ):ℝ) * x^k) x := by
        simpa only [Nat.add_sub_cancel_right]
          using (hasDerivAt_pow (k+1) x)
      have hsum := hmul.add hpow
      convert hsum using 1
      · funext y
        simp only [thetaGammaBinPolyR, Pi.add_apply]
      · simp only [thetaGammaBinPolyR]
        ring

/-- The exact elementary antiderivative for the Gamma(k+1,1)
density. The polynomial recurrence makes all k uniform. -/
theorem thetaGammaBinPrimitive_hasDerivAt (k : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        -(Real.exp (-y) * thetaGammaBinPolyR k y))
      (Real.exp (-x) * x^k) x := by
  have hExp :
      HasDerivAt (fun y : ℝ => Real.exp (-y))
        (-Real.exp (-x)) x := by
    simpa using ((hasDerivAt_id x).neg).exp
  have hP := thetaGammaBinPolyR_hasDerivAt k x
  have hprod := hExp.mul hP
  convert hprod.neg using 1 <;> ring

/-- EXACT finite-bin moment formula, valid for any integer k
and any real integration endpoints (even without L≤U).

This proof simply reuses Mathlib's FTC with a previously
proved explicit antiderivative, not a numerical quadrature
assumption. -/
theorem thetaGammaBinIntegral_exact
    (k : ℕ) (L U : ℝ) :
    (∫ w in L..U, Real.exp (-w) * w^k) =
      Real.exp (-L) * thetaGammaBinPolyR k L -
        Real.exp (-U) * thetaGammaBinPolyR k U := by
  have hD : ∀ w ∈ Set.uIcc L U,
      HasDerivAt
        (fun z : ℝ =>
          -(Real.exp (-z) * thetaGammaBinPolyR k z))
        (Real.exp (-w) * w^k) w := by
    intro w _
    exact thetaGammaBinPrimitive_hasDerivAt k w
  have hcont : Continuous (fun w : ℝ =>
      Real.exp (-w) * w^k) := by fun_prop
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      hD (hcont.intervalIntegrable L U)
  convert hFTC using 1 <;> ring

end W5
