import Nuttall.PsiCompactRemainder

namespace Nuttall

open scoped BigOperators

/-- Uniform entry-wise remainder for the compact rank-seven grid.
All grid cells have half-width at most 1/256. -/
theorem psiOne_compact_scaled_entry_error_le (l : ℕ) (hl : l ≤ 12)
    {c h v : ℝ} (ha : 0 ≤ c-h) (hb : c+h ≤ 2)
    (hh : 0 ≤ h) (hh' : h ≤ 1/256) (hv : |v| ≤ 1) :
    |(1/16:ℝ)^l * iteratedDeriv l (psi 1) (c+h*v) -
      ∑ k ∈ Finset.range 25, ((1/16:ℝ)^l * h^k / (k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) c) * v^k| ≤ (1:ℝ)/10^19 := by
  have hTaylor : (1/16:ℝ)^l * cellTaylor (iteratedDeriv l (psi 1)) 24 c h v =
      ∑ k ∈ Finset.range 25, ((1/16:ℝ)^l * h^k / (k.factorial:ℝ) *
        iteratedDeriv (l+k) (psi 1) c) * v^k := by
    rw [cellTaylor, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDeriv_iteratedDeriv_eq, Nat.add_comm k l]
    ring
  rw [← hTaylor, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1/16:ℝ)^l)]
  refine (mul_le_mul_of_nonneg_left
    (psiOne_jet_cellTaylor_error_le l 24 ha hb hh hv) (by positivity)).trans ?_
  have hp : h^25 ≤ (1/256:ℝ)^25 := pow_le_pow_left₀ hh hh' _
  refine le_trans ?_ (show (1/16:ℝ)^l *
    (((((24+l).factorial:ℝ) * 8^(24+l)) * 10^6) * (1/256:ℝ)^25 /
      ((Nat.factorial 25:ℕ):ℝ)) ≤ (1:ℝ)/10^19 by
      interval_cases l <;> norm_num [Nat.factorial])
  gcongr

#print axioms psiOne_compact_scaled_entry_error_le

end Nuttall
