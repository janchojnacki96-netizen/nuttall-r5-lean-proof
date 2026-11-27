import Nuttall.ShiftedMomentBounds
import Nuttall.MomentWeightCalculus

namespace Nuttall

open Filter
open scoped BigOperators Topology

theorem shiftedMomentTerm_succ_eq_posPart (j n : ℕ) (hn : 0 < n) (x : ℝ) :
    shiftedMomentTerm (j+1) n x =
      tailMomentWeight (j+1) (max (x-thetaKnot n) 0) / Real.sqrt (n:ℝ) := by
  by_cases hx : thetaKnot n < x
  · rw [shiftedMomentTerm, ite_eq_left ⟨hn, hx⟩, max_eq_left (sub_nonneg.2 hx.le)]
  · rw [shiftedMomentTerm, ite_eq_right (fun h => hx h.2),
      max_eq_right (sub_nonpos.2 (le_of_not_gt hx)), tailMomentWeight_succ_zero, zero_div]

/-- Positive-index summands extend continuously through their own cutoff. -/
theorem continuous_shiftedMomentTerm_succ (j n : ℕ) : Continuous (shiftedMomentTerm (j+1) n) := by
  by_cases hn : 0 < n
  · rw [funext (shiftedMomentTerm_succ_eq_posPart j n hn)]
    unfold tailMomentWeight
    fun_prop
  · have heq : shiftedMomentTerm (j+1) n = fun _ => 0 := by
      funext u
      simp [shiftedMomentTerm, hn]
    rw [heq]
    exact continuous_const

/-- At a fixed node the whole sum agrees locally with a continuous finite sum. -/
theorem continuous_shiftedMoment_succ (j : ℕ) : Continuous (shiftedMoment (j+1)) := by
  apply continuous_iff_continuousAt.2
  intro u
  let N := ⌈Real.exp (2*(u+1))⌉₊
  have hcont : Continuous (shiftedMomentTruncated (j+1) N) := by
    unfold shiftedMomentTruncated
    exact continuous_finsetSum _ (fun n _ => continuous_shiftedMomentTerm_succ j n)
  have hn : ∀ᶠ v in 𝓝 u, v < u+1 := eventually_lt_nhds (by linarith)
  have heq : shiftedMomentTruncated (j+1) N =ᶠ[𝓝 u] shiftedMoment (j+1) := by
    filter_upwards [hn] with v hv
    apply shiftedMomentTruncated_eq_of_ge_ceil
    exact Nat.ceil_mono (Real.exp_le_exp.2 (by linarith))
  exact hcont.continuousAt.congr heq

#print axioms continuous_shiftedMoment_succ

end Nuttall
