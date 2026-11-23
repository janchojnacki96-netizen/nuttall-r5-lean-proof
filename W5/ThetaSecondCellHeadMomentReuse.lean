import W5.ThetaSecondCellHeadFiniteMajorants
import W5.ThetaCoarseGammaMomentBoxes

/-!
# Exact reuse of the EXISTING real-sound quarter-Gamma moment bound

The computable K majorant must not introduce another proof of the
Gamma integrals. Its rational upper moment is definitionally the
upper endpoint of the existing proved per-index moment box.

This module explicitly records that bridge for ALL k and n>0,
so the remaining original n=2,3 term estimate can reuse the old
Mathlib moment theorem verbatim.
-/

namespace W5

/-- The new computational head-moment expression is exactly the
old proved quarter-Gamma upper interval endpoint. -/
theorem thetaHeadMomentUpper_eq_quarterGammaHi
    (b : ℚ) (n k : ℕ) :
    thetaHeadMomentUpper b n k =
      (thetaNthQuarterGammaMomentBox b n k).hi := by
  simp only [thetaHeadMomentUpper,
    thetaNthQuarterGammaMomentBox, div_pow]
  ring

/-- The ACTUAL weighted theta moment has the claimed rational
upper majorant on any positive-index cell. No new integral proof. -/
theorem thetaHeadMomentUpper_real_sound
    (b : ℚ) (x : ℝ)
    (hx : 0 ≤ x) (hxb : x ≤ (b : ℝ))
    (hb : (b : ℝ) ≤ 1)
    (n k : ℕ) (hn : 0 < n) :
    thetaAuditedOneWeightedMoment (x/(n:ℝ)) k ≤
      (thetaHeadMomentUpper b n k : ℝ) := by
  rw [thetaHeadMomentUpper_eq_quarterGammaHi]
  exact (thetaNthQuarterGammaMomentBox_containsReal
    b x hx hxb hb n k hn).2

end W5
