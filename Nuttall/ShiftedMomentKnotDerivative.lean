import Nuttall.ShiftedMomentContinuity
import Nuttall.ShiftedMomentDerivatives

namespace Nuttall

open Filter Set
open scoped Topology BigOperators

private theorem two_weight_positive_part_hasDerivAt (j : ℕ) (x : ℝ) :
    HasDerivAt (fun t => tailMomentWeight (j+2) (max t 0))
      (tailMomentWeight (j+1) (max x 0)) x := by
  let g (t : ℝ) := tailMomentWeight (j+2) (max t 0)
  have hleft (t : ℝ) (ht : t ∈ Iic (0:ℝ)) : g t = 0 := by
    rw [show g t = tailMomentWeight (j+2) (max t 0) from rfl,
      max_eq_right ht, tailMomentWeight_succ_zero]
  have hright (t : ℝ) (ht : t ∈ Ici (0:ℝ)) : g t = tailMomentWeight (j+2) t := by
    rw [show g t = tailMomentWeight (j+2) (max t 0) from rfl, max_eq_left ht]
  change HasDerivAt g _ x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [max_eq_right hx.le, tailMomentWeight_succ_zero]
    apply (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq
    exact (eventually_lt_nhds hx).mono (fun t ht => hleft t ht.le)
  · rw [max_self, tailMomentWeight_succ_zero]
    have hl : HasDerivWithinAt g 0 (Iic 0) 0 :=
      (hasDerivAt_const (0:ℝ) (0:ℝ)).hasDerivWithinAt.congr hleft (hleft 0 (mem_Iic.mpr le_rfl))
    have hr : HasDerivWithinAt g 0 (Ici 0) 0 := by
      have h := tailMomentWeight_succ_hasDerivAt (j+1) (0:ℝ)
      rw [tailMomentWeight_succ_zero] at h
      exact h.hasDerivWithinAt.congr hright (hright 0 (mem_Ici.mpr le_rfl))
    apply hasDerivWithinAt_univ.1
    rw [← Iic_union_Ici]
    exact hl.union hr
  · rw [max_eq_left hx.le]
    apply (tailMomentWeight_succ_hasDerivAt (j+1) x).congr_of_eventuallyEq
    exact (eventually_gt_nhds hx).mono (fun t ht => hright t ht.le)

/-- At indices at least two the strict cutoff creates no derivative jump. -/
theorem shiftedMomentTerm_succ_succ_hasDerivAt (j n : ℕ) (u : ℝ) :
    HasDerivAt (shiftedMomentTerm (j+2) n) (shiftedMomentTerm (j+1) n u) u := by
  by_cases hn : 0 < n
  · have h := ((two_weight_positive_part_hasDerivAt j (u-thetaKnot n)).comp u
      ((hasDerivAt_id u).sub_const (thetaKnot n))).div_const (Real.sqrt (n:ℝ))
    have he (l : ℕ) : shiftedMomentTerm (l+1) n =
        fun x => tailMomentWeight (l+1) (max (x-thetaKnot n) 0) / Real.sqrt (n:ℝ) :=
      funext (shiftedMomentTerm_succ_eq_posPart l n hn)
    rw [he (j+1), he j]
    simpa only [id_eq, mul_one, Function.comp_def] using h
  · have hzero (m : ℕ) : shiftedMomentTerm m n = fun _ => 0 := by
      funext v
      simp [shiftedMomentTerm, hn]
    rw [hzero, hzero]
    exact hasDerivAt_const u 0

theorem shiftedMoment_succ_succ_hasDerivAt (j : ℕ) (u : ℝ) :
    HasDerivAt (shiftedMoment (j+2)) (shiftedMoment (j+1) u) u := by
  let N := ⌈Real.exp (2*(u+1))⌉₊
  have htr (l : ℕ) : shiftedMomentTruncated l N =ᶠ[𝓝 u] shiftedMoment l := by
    filter_upwards [eventually_lt_nhds (show u < u+1 by linarith)] with v hv
    exact shiftedMomentTruncated_eq_of_ge_ceil _ _ _ (Nat.ceil_mono (Real.exp_le_exp.2 (by linarith)))
  have h : HasDerivAt (shiftedMomentTruncated (j+2) N) (shiftedMomentTruncated (j+1) N u) u := by
    unfold shiftedMomentTruncated
    exact HasDerivAt.fun_sum (fun n _ => shiftedMomentTerm_succ_succ_hasDerivAt j n u)
  rw [(htr (j+1)).eq_of_nhds] at h
  exact h.congr_of_eventuallyEq (htr (j+2)).symm

/-- The derivative formula is global as long as at least one power remains. -/
theorem iteratedDeriv_shiftedMoment_of_lt {j k : ℕ} (hk : k < j) (u : ℝ) :
    iteratedDeriv k (shiftedMoment j) u = shiftedMoment (j-k) u := by
  induction k generalizing j u with
  | zero => simp
  | succ k ih =>
    have hfun : iteratedDeriv k (shiftedMoment j) = shiftedMoment (j-k) :=
      funext (fun v => ih (by omega) v)
    rw [iteratedDeriv_succ, hfun, show j-k = (j-(k+1))+1 by omega,
      show j-(k+1) = (j-(k+2))+1 by omega]
    exact (shiftedMoment_succ_succ_hasDerivAt (j-(k+2)) u).deriv

#print axioms iteratedDeriv_shiftedMoment_of_lt

end Nuttall
