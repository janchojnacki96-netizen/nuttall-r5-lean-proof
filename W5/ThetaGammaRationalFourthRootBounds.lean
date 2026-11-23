import W5.ThetaMomentFourthRootChordTangent
import W5.VerifiedIntervalRealSemantics

/-!
# One completely rational certificate for every fourth-root endpoint

The recentered Gamma-bin quadrature has a fourth root at each
rational w-bin endpoint. These roots should NOT be estimated with
untrusted floating point. Instead, supply rational l,u with four
purely rational checks:

  0 <= l, 0 <= u, l^4 <= t, t <= u^4.

This generic Mathlib proof establishes immediately
  l <= t^(1/4) <= u

for the ORIGINAL real fourth root at every endpoint. Exact integer
arithmetic can check millions of such inequalities in one Boolean
pass, without any new real transcendental numerical axiom.
-/

namespace W5

/-- The positive-fourth-power cancellation is already implicit
in the existing theta fourth-root proof. This helper exposes it
for the rational bounds of all future w-bin endpoints. -/
theorem thetaFourthRoot_fourthPower_cancel
    (x : ℝ) (hx : 0 ≤ x) :
    (x^4)^((1:ℝ)/4) = x := by
  simpa only [one_div] using
    (Real.pow_rpow_inv_natCast hx (by decide : (4:ℕ) ≠ 0))

/-- A single real-semantic QInterval proof from only rational fourth
power comparisons. This works for every original theta w-bin and
every nonnegative fourth-root argument, with no numerical integration. -/
theorem thetaFourthRoot_rational_power_box_containsReal
    (t : ℝ) (ht : 0 ≤ t)
    (l u : ℚ) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : ((l:ℝ)^4) ≤ t)
    (hhi : t ≤ ((u:ℝ)^4)) :
    QInterval.ContainsReal (⟨l,u⟩ : QInterval)
      (t^((1:ℝ)/4)) := by
  have hlR : (0:ℝ) ≤ (l:ℝ) := by exact_mod_cast hl
  have huR : (0:ℝ) ≤ (u:ℝ) := by exact_mod_cast hu
  change (l:ℝ) ≤ t^((1:ℝ)/4) ∧
    t^((1:ℝ)/4) ≤ (u:ℝ)
  constructor
  · calc
      (l:ℝ) = ((l:ℝ)^4)^((1:ℝ)/4) :=
        (thetaFourthRoot_fourthPower_cancel _ hlR).symm
      _ ≤ t^((1:ℝ)/4) :=
        Real.rpow_le_rpow (pow_nonneg hlR 4) hlo (by norm_num)
  · calc
      t^((1:ℝ)/4) ≤ ((u:ℝ)^4)^((1:ℝ)/4) :=
        Real.rpow_le_rpow ht hhi (by norm_num)
      _ = (u:ℝ) := thetaFourthRoot_fourthPower_cancel _ huR

/-- The same soundness API when the target argument is itself an
exact rational. All proof obligations are now decidable by exact
rational arithmetic, ready for one bulk native_decide check. -/
theorem thetaFourthRoot_rational_arg_box_containsReal
    (t l u : ℚ)
    (ht : 0 ≤ t) (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : l^4 ≤ t) (hhi : t ≤ u^4) :
    QInterval.ContainsReal (⟨l,u⟩:QInterval)
      ((t:ℝ)^((1:ℝ)/4)) := by
  have htR : (0:ℝ) ≤ (t:ℝ) := by exact_mod_cast ht
  have hlR : ((l:ℝ)^4) ≤ (t:ℝ) := by
    exact_mod_cast hlo
  have huR : (t:ℝ) ≤ ((u:ℝ)^4) := by
    exact_mod_cast hhi
  exact thetaFourthRoot_rational_power_box_containsReal
    (t:ℝ) htR l u hl hu hlR huR

end W5
