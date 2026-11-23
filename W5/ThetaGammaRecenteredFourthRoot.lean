import W5.ThetaMomentFourthRootChordTangent
import W5.ThetaAuditedMomentGammaCubicUpper
import W5.ThetaAuditedMomentGammaQuadraticLower

/-!
# Locally recentered cubic-error Gamma envelopes

The global quadratic/cubic bounds on (1+u)^(1/4) are TOO WIDE for
the k=8 weighted Gamma moments (at x=145/256 their global interval
can have width exceeding 70,000).

Instead split the *integration variable* w into small intervals
[L,U], and on each bin factor EXACTLY

  (1+q*w)^(1/4) = A^(1/4)*(1+v)^(1/4)
  A=1+q*L, v=q*(w-L)/A >= 0.

Reusing the EXISTING fully checked global quartic-root inequalities
gives a local quadratic lower and cubic upper. Their exact
difference is (7/128)*A^(1/4)*v^3, O((U-L)^3),
rather than the global envelope error growing with w^3.

No new derivative or Taylor theorem and no extra mathematical
assumption. This is one reusable mathematical building block for
all 48 cells and all nine weighted Gamma moments. The finite-bin
integral certification and numerical LDL checks remain separate.
-/

namespace W5

/-- The positive base of the local shifted fourth-root expansion. -/
def thetaGammaBinBase (q L : ℝ) : ℝ := 1+q*L

/-- The local nonnegative Taylor parameter in a Gamma integration bin. -/
noncomputable def thetaGammaBinOffset (q L w : ℝ) : ℝ :=
  q*(w-L)/(thetaGammaBinBase q L)

/-- Positivity of both parameters for every original theta w-bin. -/
theorem thetaGammaBinBase_pos (q L : ℝ)
    (hq : 0 ≤ q) (hL : 0 ≤ L) :
    0 < thetaGammaBinBase q L := by
  dsimp [thetaGammaBinBase]
  have h := mul_nonneg hq hL
  linarith

theorem thetaGammaBinOffset_nonneg (q L w : ℝ)
    (hq : 0 ≤ q) (hL : 0 ≤ L) (hLw : L ≤ w) :
    0 ≤ thetaGammaBinOffset q L w := by
  unfold thetaGammaBinOffset
  exact div_nonneg (mul_nonneg hq (sub_nonneg.mpr hLw))
    (thetaGammaBinBase_pos q L hq hL).le

/-- Exact factorization; the local expansion does not approximate
the original theta fourth root. -/
theorem thetaGammaBinBase_mul_offset (q L w : ℝ)
    (hq : 0 ≤ q) (hL : 0 ≤ L) :
    thetaGammaBinBase q L *
      (1+thetaGammaBinOffset q L w) = 1+q*w := by
  have hA := thetaGammaBinBase_pos q L hq hL
  unfold thetaGammaBinOffset
  field_simp [ne_of_gt hA]
  dsimp [thetaGammaBinBase]
  ring

/-- Use Mathlib Real.mul_rpow to preserve the exact factorization
of the real fourth root before any lower/upper approximation. -/
theorem thetaGammaBinFourthRoot_factor (q L w : ℝ)
    (hq : 0 ≤ q) (hL : 0 ≤ L) (hLw : L ≤ w) :
    (1+q*w)^((1:ℝ)/4) =
      (thetaGammaBinBase q L)^((1:ℝ)/4) *
        (1+thetaGammaBinOffset q L w)^((1:ℝ)/4) := by
  have hA := thetaGammaBinBase_pos q L hq hL
  have hv := thetaGammaBinOffset_nonneg q L w hq hL hLw
  rw [← thetaGammaBinBase_mul_offset q L w hq hL,
    Real.mul_rpow hA.le (by linarith : 0 ≤ 1+thetaGammaBinOffset q L w)]

/-- One LOCAL analytic two-sided bound on the original theta
integrand fourth root. The upper and lower formulas have a
gap of order (w-L)^3 on every w-bin, unlike the global cubic
versus quadratic approximations. -/
theorem thetaGammaBinFourthRoot_recentered_bounds
    (q L w : ℝ) (hq : 0 ≤ q) (hL : 0 ≤ L) (hLw : L ≤ w) :
    let A := thetaGammaBinBase q L
    let v := thetaGammaBinOffset q L w
    A^((1:ℝ)/4)*(1+v/4-3*v^2/32) ≤
      (1+q*w)^((1:ℝ)/4) ∧
    (1+q*w)^((1:ℝ)/4) ≤
      A^((1:ℝ)/4)*(1+v/4-3*v^2/32+7*v^3/128) := by
  let A := thetaGammaBinBase q L
  let v := thetaGammaBinOffset q L w
  have hv : 0 ≤ v :=
    thetaGammaBinOffset_nonneg q L w hq hL hLw
  have hA : 0 ≤ A^((1:ℝ)/4) :=
    Real.rpow_nonneg (thetaGammaBinBase_pos q L hq hL).le _
  have hRoot : (1+q*w)^((1:ℝ)/4) =
      A^((1:ℝ)/4)*(1+v)^((1:ℝ)/4) :=
    thetaGammaBinFourthRoot_factor q L w hq hL hLw
  change A^((1:ℝ)/4)*(1+v/4-3*v^2/32) ≤
      (1+q*w)^((1:ℝ)/4) ∧
    (1+q*w)^((1:ℝ)/4) ≤
      A^((1:ℝ)/4)*(1+v/4-3*v^2/32+7*v^3/128)
  rw [hRoot]
  exact ⟨
    mul_le_mul_of_nonneg_left
      (thetaFourthRoot_one_add_quadratic_lower v hv) hA,
    mul_le_mul_of_nonneg_left
      (thetaFourthRoot_one_add_cubic_upper v hv) hA⟩

/-- The width is EXACTLY cubic in the local offset v, not merely
an O-notation heuristic. This quantifies the improvement expected
from subdividing the single w-integration axis. -/
theorem thetaGammaBinFourthRoot_envelope_width
    (A v : ℝ) :
    A^((1:ℝ)/4)*(1+v/4-3*v^2/32+7*v^3/128) -
      A^((1:ℝ)/4)*(1+v/4-3*v^2/32) =
        A^((1:ℝ)/4)*(7*v^3/128) := by
  ring

end W5
