import W5.Statement
import Mathlib.Analysis.Real.Pi.Bounds

namespace W5
/-- x(t)=1/sqrt(pi*exp(4t)) lies in (0,145/256) for t≥0. -/
theorem xOfT_positive_and_bounded (t : ℝ) (ht : 0 ≤ t) :
    0 < xOfT t ∧ xOfT t < (145 : ℝ) / 256 := by
  have hypos : 0 < Real.pi * Real.exp (4 * t) :=
    mul_pos Real.pi_pos (Real.exp_pos _)
  have hspos : 0 < Real.sqrt (Real.pi * Real.exp (4 * t)) :=
    Real.sqrt_pos.2 hypos
  have hpos : 0 < xOfT t := by
    unfold xOfT
    exact one_div_pos.mpr hspos
  have h4t : 0 ≤ (4 : ℝ) * t := by positivity
  have he : 1 ≤ Real.exp (4 * t) := by
    have h := Real.add_one_le_exp (4 * t)
    linarith
  have hmul : Real.pi ≤ Real.pi * Real.exp (4 * t) := by
    have hm := mul_nonneg (le_of_lt Real.pi_pos)
      (show 0 ≤ Real.exp (4 * t) - 1 by linarith)
    nlinarith
  have hpi : ((256 : ℝ) / 145) ^ 2 < Real.pi := by
    nlinarith [Real.pi_gt_d2]
  have hy : ((256 : ℝ) / 145) ^ 2 < Real.pi * Real.exp (4 * t) := by
    linarith
  have hsqr : (Real.sqrt (Real.pi * Real.exp (4 * t))) ^ 2 =
      Real.pi * Real.exp (4 * t) := Real.sq_sqrt (le_of_lt hypos)
  have hlarge : (256 : ℝ) / 145 < Real.sqrt (Real.pi * Real.exp (4 * t)) := by
    by_contra hn
    have hle : Real.sqrt (Real.pi * Real.exp (4 * t)) ≤ (256 : ℝ) / 145 :=
      le_of_not_gt hn
    have hsign : 0 ≤ ((256 : ℝ) / 145 -
        Real.sqrt (Real.pi * Real.exp (4 * t))) *
        ((256 : ℝ) / 145 +
        Real.sqrt (Real.pi * Real.exp (4 * t))) := by
      apply mul_nonneg
      · linarith
      · positivity
    nlinarith [hsqr, hy]
  have hbound : 1 / Real.sqrt (Real.pi * Real.exp (4 * t)) <
      (145 : ℝ) / 256 := by
    apply (div_lt_iff₀ hspos).mpr
    nlinarith [hlarge]
  exact ⟨hpos, by simpa [xOfT] using hbound⟩

theorem xOfT_in_certificate_range (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ xOfT t ∧ xOfT t ≤ (145 : ℝ) / 256 := by
  obtain ⟨h0, h1⟩ := xOfT_positive_and_bounded t ht
  exact ⟨le_of_lt h0, le_of_lt h1⟩
end W5
