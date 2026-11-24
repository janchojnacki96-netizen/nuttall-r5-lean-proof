import W5.ThetaGammaAutoRootGrid
import W5.ThetaGammaFiniteBinIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Exact infinite Gamma tail from an existing Mathlib finite-bin identity

For k≥0 and H≥0, the ordinary incomplete Gamma tail has the closed
form: integral from H to infinity of exp(-w) w^k equals exp(-H)*P_k(H).

Here P_k is already implemented and its finite integral is proved
in ThetaGammaFiniteBinIntegral. The only new integration step is
Mathlib intervalIntegral.integral_interval_add_Ioi, connecting
previously proven full factorial and finite-bin integrals.

For rational H, P_k(H) is rational and exp(-H) already has a
real-sound certified rational interval in the project.
-/

namespace W5
open MeasureTheory

/-- The Gamma tail polynomial at zero equals k! exactly. -/
theorem thetaGammaBinPolyR_zero_factorial (k : ℕ) :
    thetaGammaBinPolyR k 0 = (Nat.factorial k : ℝ) := by
  induction k with
  | zero => simp [thetaGammaBinPolyR]
  | succ k ih =>
      simp [thetaGammaBinPolyR, ih, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add]

/-- Exact evaluation of the TRUE infinite Gamma tail. -/
theorem thetaGammaExpMoment_tail_exact
    (k : ℕ) (H : ℝ) (hH : 0 ≤ H) :
    (∫ w in Set.Ici H, Real.exp (-w) * w^k ∂volume) =
      Real.exp (-H) * thetaGammaBinPolyR k H := by
  have hComm :
      (fun w : ℝ => Real.exp (-w) * w^k) =
        (fun w : ℝ => w^k * Real.exp (-w)) := by
    funext w
    ring
  have h0 : IntegrableOn
      (fun w : ℝ => Real.exp (-w) * w^k)
      (Set.Ioi (0:ℝ)) volume := by
    rw [hComm]
    exact thetaAuditedCorrectionGammaMoment_integrable k
  have hHInt : IntegrableOn
      (fun w : ℝ => Real.exp (-w) * w^k)
      (Set.Ioi H) volume :=
    h0.mono_set (Set.Ioi_subset_Ioi hH)
  have hSplit :
      (∫ w in (0:ℝ)..H, Real.exp (-w) * w^k) +
      (∫ w in Set.Ioi H, Real.exp (-w) * w^k ∂volume) =
      (∫ w in Set.Ioi (0:ℝ), Real.exp (-w) * w^k ∂volume) :=
    intervalIntegral.integral_interval_add_Ioi h0 hHInt
  have hFull :
      (∫ w in Set.Ioi (0:ℝ), Real.exp (-w) * w^k ∂volume) =
        (Nat.factorial k : ℝ) := by
    rw [hComm]
    exact thetaAuditedCorrectionGammaMoment k
  have hBin := thetaGammaBinIntegral_exact k 0 H
  rw [integral_Ici_eq_integral_Ioi]
  rw [hBin, hFull, neg_zero, Real.exp_zero,
      one_mul, thetaGammaBinPolyR_zero_factorial] at hSplit
  linarith

end W5
