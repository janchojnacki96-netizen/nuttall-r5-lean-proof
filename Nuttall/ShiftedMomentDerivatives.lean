import Nuttall.MomentWeightCalculus
import Nuttall.ShiftedMomentBounds

namespace Nuttall

open Filter
open scoped BigOperators Topology

/-- The positive theta indices with knots strictly below the node. -/
noncomputable def activeThetaIndices (u : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range ⌈Real.exp (2*u)⌉₊).filter (fun n => 0 < n ∧ thetaKnot n < u)

theorem mem_activeThetaIndices {n : ℕ} {u : ℝ} :
    n ∈ activeThetaIndices u ↔ 0 < n ∧ thetaKnot n < u := by
  classical
  unfold activeThetaIndices
  rw [Finset.mem_filter, Finset.mem_range]
  exact and_iff_right_of_imp (fun h =>
    Nat.lt_ceil.2 ((thetaKnot_lt_iff n h.1 u).1 h.2))

private theorem shiftedMoment_eq_sum_active (j : ℕ) (u : ℝ) :
    shiftedMoment j u =
      ∑ n ∈ activeThetaIndices u, tailMomentWeight j (u-thetaKnot n) / Real.sqrt (n : ℝ) := by
  classical
  simp only [shiftedMoment, shiftedMomentTerm_tsum_eq_sum, activeThetaIndices,
    Finset.sum_filter, shiftedMomentTerm]

/-- Away from the knots, a neighborhood uses the same finite set of theta indices. -/
theorem eventuallyEq_activeThetaIndices {u : ℝ}
    (hu : ∀ n : ℕ, 0 < n → u ≠ thetaKnot n) :
    (fun v => activeThetaIndices u) =ᶠ[𝓝 u] activeThetaIndices := by
  let N := ⌈Real.exp (2*(u+1))⌉₊
  have hbound : ∀ᶠ v in 𝓝 u, v < u+1 := eventually_lt_nhds (by linarith)
  have hcut {w : ℝ} (hw : w ≤ u+1) {n : ℕ} (hn : n ∈ activeThetaIndices w) :
      n ∈ Finset.range N := by
    have h := mem_activeThetaIndices.mp hn
    exact Finset.mem_range.mpr (Nat.lt_ceil.2
      (((thetaKnot_lt_iff n h.1 w).1 h.2).trans_le (Real.exp_le_exp.mpr (by linarith))))
  have hstable : ∀ᶠ v in 𝓝 u, ∀ n ∈ Finset.range N,
      (0 < n ∧ thetaKnot n < u) ↔ (0 < n ∧ thetaKnot n < v) := by
    apply (Finset.eventually_all _).2
    intro n _
    by_cases hn : 0 < n
    · by_cases ha : thetaKnot n < u
      · exact (eventually_gt_nhds ha).mono (fun v hv => by simp [hn, ha, hv])
      · have hb : u < thetaKnot n := lt_of_le_of_ne (le_of_not_gt ha) (hu n hn)
        exact (eventually_lt_nhds hb).mono (fun v hv => by simp [hn, ha, hv.not_gt])
    · exact Eventually.of_forall (fun _ => by simp [hn])
  filter_upwards [hbound, hstable] with v hv hstable
  ext n
  constructor
  · intro hn
    exact mem_activeThetaIndices.mpr
      ((hstable n (hcut (by linarith) hn)).mp (mem_activeThetaIndices.mp hn))
  · intro hn
    exact mem_activeThetaIndices.mpr
      ((hstable n (hcut hv.le hn)).mpr (mem_activeThetaIndices.mp hn))

private theorem shifted_weight_sum_succ_hasDerivAt (j : ℕ) (s : Finset ℕ) (u : ℝ) :
    HasDerivAt (fun v : ℝ => ∑ n ∈ s, tailMomentWeight (j+1) (v-thetaKnot n) / Real.sqrt (n : ℝ))
      (∑ n ∈ s, tailMomentWeight j (u-thetaKnot n) / Real.sqrt (n : ℝ)) u := by
  apply HasDerivAt.fun_sum
  intro n _
  simpa using (((tailMomentWeight_succ_hasDerivAt j (u-thetaKnot n)).comp u
    ((hasDerivAt_id u).sub_const (thetaKnot n))).div_const (Real.sqrt (n : ℝ)))

private theorem iteratedDeriv_shifted_weight_sum {j k : ℕ} (hk : k ≤ j) (s : Finset ℕ) :
    iteratedDeriv k (fun v : ℝ => ∑ n ∈ s, tailMomentWeight j (v-thetaKnot n) / Real.sqrt (n : ℝ)) =
      fun v => ∑ n ∈ s, tailMomentWeight (j-k) (v-thetaKnot n) / Real.sqrt (n : ℝ) := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    have h' : k ≤ j := by omega
    funext v
    rw [iteratedDeriv_succ, ih h', show j-k = (j-(k+1))+1 by omega]
    exact (shifted_weight_sum_succ_hasDerivAt (j-(k+1)) s v).deriv

/-- Off the knots, differentiating a shifted moment lowers its index. -/
theorem iteratedDeriv_shiftedMoment {j k : ℕ} (hk : k ≤ j) {u : ℝ}
    (hu : ∀ n : ℕ, 0 < n → u ≠ thetaKnot n) :
    iteratedDeriv k (shiftedMoment j) u = shiftedMoment (j-k) u := by
  have heq : shiftedMoment j =ᶠ[𝓝 u] fun v =>
      ∑ n ∈ activeThetaIndices u, tailMomentWeight j (v-thetaKnot n) / Real.sqrt (n : ℝ) := by
    filter_upwards [eventuallyEq_activeThetaIndices hu] with v hv
    rw [shiftedMoment_eq_sum_active, ← hv]
  rw [(heq.iteratedDeriv k).eq_of_nhds, iteratedDeriv_shifted_weight_sum hk, shiftedMoment_eq_sum_active]

#print axioms iteratedDeriv_shiftedMoment

end Nuttall
