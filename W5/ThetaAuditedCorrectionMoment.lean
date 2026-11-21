import W5.ThetaAllCorrectionSummabilityFubini
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Exact weighted exponential moment for the original theta correction

For the integral correction in the original theta certificate, the
polynomial envelope naturally produces the integrable weight
`(1+w)^13 * exp (-w)` on `(0, infinity)`.

This file proves its exact integral using the ALREADY FORMALIZED
Gamma integral and factorial identity from Mathlib. In particular,
the numerical bound is certified by Lean arithmetic, not supplied
by the external Python interval checker.

No estimate for the actual theta correction summand is claimed
until its pointwise polynomial/exponential domination has been
proved and connected to this exact moment.
-/

namespace W5
open MeasureTheory

/-- The positive half-line exponential moments are factorials.
This is precisely Mathlib's Gamma integral at a natural argument. -/
theorem thetaAuditedCorrectionGammaMoment (k : ℕ) :
    (∫ w : ℝ in Set.Ioi (0 : ℝ),
      w^k * Real.exp (-w)) = (Nat.factorial k : ℝ) := by
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (k : ℝ) + 1) (r := (1 : ℝ)) hk (by norm_num)
  simpa [Real.rpow_natCast, Real.Gamma_nat_eq_factorial] using h

/-- Each exponential monomial is integrable on the positive half-line.
This follows from the already-proved nonzero Gamma integral. -/
theorem thetaAuditedCorrectionGammaMoment_integrable (k : ℕ) :
    IntegrableOn (fun w : ℝ => w^k * Real.exp (-w))
      (Set.Ioi (0 : ℝ)) volume := by
  apply IntegrableOn.of_integral_ne_zero
  rw [thetaAuditedCorrectionGammaMoment]
  positivity

/-- Exact finite exponential moment of the degree-13 envelope.
The right side is the exact integer sum
`sum_{k=0}^{13} (13 choose k) * k!`. -/
theorem thetaAuditedCorrectionShiftedMoment :
    (∫ w : ℝ in Set.Ioi (0 : ℝ),
      (w+1)^13 * Real.exp (-w)) = (16926797486 : ℝ) := by
  let μ := volume.restrict (Set.Ioi (0 : ℝ))
  have hterm (k : ℕ) : Integrable
      (fun w : ℝ =>
        (w^k * Real.exp (-w)) * (Nat.choose 13 k : ℝ)) μ :=
    (thetaAuditedCorrectionGammaMoment_integrable k).mul_const _
  have hbinom (w : ℝ) :
      (w+1)^13 * Real.exp (-w) =
        ∑ k ∈ Finset.range (13+1),
          (w^k * Real.exp (-w)) * (Nat.choose 13 k : ℝ) := by
    rw [add_pow, Finset.sum_mul]
    simp only [one_pow, mul_one]
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    (∫ w : ℝ in Set.Ioi (0 : ℝ),
      (w+1)^13 * Real.exp (-w)) =
        ∫ w : ℝ in Set.Ioi (0 : ℝ),
          ∑ k ∈ Finset.range (13+1),
            (w^k * Real.exp (-w)) * (Nat.choose 13 k : ℝ) := by
          apply integral_congr_ae
          filter_upwards [] with w
          exact hbinom w
    _ = ∑ k ∈ Finset.range (13+1),
        (∫ w : ℝ in Set.Ioi (0 : ℝ),
          (w^k * Real.exp (-w)) * (Nat.choose 13 k : ℝ)) := by
          exact integral_finsetSum (Finset.range (13+1)) (fun k _ => hterm k)
    _ = ∑ k ∈ Finset.range (13+1),
        (Nat.factorial k : ℝ) * (Nat.choose 13 k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k _
          rw [integral_mul_const, thetaAuditedCorrectionGammaMoment]
    _ = (16926797486 : ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.choose, Nat.factorial]

/-- A strict, exact-arithmetic moment bound with ample room for
the original audit's 3e10 correction multiplier. -/
theorem thetaAuditedCorrectionShiftedMoment_lt_budget :
    (∫ w : ℝ in Set.Ioi (0 : ℝ),
      (w+1)^13 * Real.exp (-w)) < (30000000000 : ℝ) := by
  rw [thetaAuditedCorrectionShiftedMoment]
  norm_num

end W5
