import Nuttall.ShiftedMomentWronskianAtKnots
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

namespace Nuttall

open Filter MeasureTheory Set
open scoped Topology BigOperators ContDiff

/-- Outside the theta knots the shifted moment is locally a polynomial. -/
theorem contDiffAt_shiftedMoment_off_knots (j : ℕ) {x : ℝ} {s : ℕ∞ω}
    (hx : ∀ n : ℕ, 0 < n → x ≠ thetaKnot n) :
    ContDiffAt ℝ s (shiftedMoment j) x := by
  have heq : shiftedMoment j =ᶠ[𝓝 x] fun y =>
      ∑ n ∈ activeThetaIndices x, tailMomentWeight j (y-thetaKnot n) / Real.sqrt (n : ℝ) := by
    filter_upwards [eventuallyEq_activeThetaIndices hx] with y hy
    rw [shiftedMoment_eq_sum_active, ← hy]
  apply ContDiffAt.congr_of_eventuallyEq _ heq
  unfold tailMomentWeight
  fun_prop

/-- The globally continuous derivatives extend through every theta knot
as long as the shifted-moment index remains positive. -/
theorem contDiff_shiftedMoment_of_lt {j k : ℕ} (hk : k < j) :
    ContDiff ℝ k (shiftedMoment j) := by
  apply contDiff_nat_iff_iteratedDeriv.2
  have heq (m : ℕ) (hm : m ≤ k) : iteratedDeriv m (shiftedMoment j) =
      shiftedMoment (j-m) := funext (iteratedDeriv_shiftedMoment_of_lt (hm.trans_lt hk))
  constructor
  · intro m hm
    rw [heq m hm, show j-m = (j-m-1)+1 by omega]
    exact continuous_shiftedMoment_succ _
  · intro m hm
    rw [heq m hm.le, show j-m = (j-m-2)+2 by omega]
    exact fun x => (shiftedMoment_succ_succ_hasDerivAt _ x).differentiableAt

private theorem locallyLipschitz_shiftedMomentTerm_succ (j n : ℕ) :
    LocallyLipschitz (shiftedMomentTerm (j+1) n) := by
  by_cases hn : 0 < n
  · rw [funext (shiftedMomentTerm_succ_eq_posPart j n hn)]
    have hpoly : ContDiff ℝ 1 (fun y => tailMomentWeight (j+1) y / Real.sqrt (n:ℝ)) := by
      unfold tailMomentWeight
      fun_prop
    have hlinear : ContDiff ℝ 1 (fun x : ℝ => x-thetaKnot n) := by fun_prop
    exact hpoly.locallyLipschitz.comp (hlinear.locallyLipschitz.max_const 0)
  · have heq : shiftedMomentTerm (j+1) n = fun _ => 0 := by
      funext u
      simp [shiftedMomentTerm, hn]
    rw [heq]
    exact LocallyLipschitz.const _

/-- The positive-part polynomial formula gives local Lipschitz regularity,
including for the last continuous derivative across a knot. -/
theorem locallyLipschitz_shiftedMoment_succ (j : ℕ) :
    LocallyLipschitz (shiftedMoment (j+1)) := by
  intro x
  let N := ⌈Real.exp (2*(x+1))⌉₊
  have hsum (s : Finset ℕ) :
      LocallyLipschitz (fun y => ∑ n ∈ s, shiftedMomentTerm (j+1) n y) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (LocallyLipschitz.const (α := ℝ) (0:ℝ))
    | insert n s hn ih =>
      simp only [Finset.sum_insert hn]
      exact (locallyLipschitz_shiftedMomentTerm_succ j n).add ih
  obtain ⟨K, V, hV, hlim⟩ := hsum (Finset.range N) x
  refine ⟨K, V ∩ Iio (x+1), inter_mem hV (Iio_mem_nhds (by linarith)), ?_⟩
  have heq (y : ℝ) (hy : y ∈ V ∩ Iio (x+1)) :
      shiftedMomentTruncated (j+1) N y = shiftedMoment (j+1) y :=
    shiftedMomentTruncated_eq_of_ge_ceil _ _ _
      (Nat.ceil_mono (Real.exp_le_exp.2 (by have := hy.2; simp only [mem_Iio] at this; linarith)))
  intro y hy z hz
  rw [← heq y hy, ← heq z hz]
  exact hlim hy.1 hz.1

theorem absolutelyContinuousOnInterval_iteratedDeriv_shiftedMoment {j k : ℕ} (hk : k < j)
    (a b : ℝ) : AbsolutelyContinuousOnInterval (iteratedDeriv k (shiftedMoment j)) a b := by
  rw [funext (iteratedDeriv_shiftedMoment_of_lt hk), show j-k = (j-k-1)+1 by omega]
  obtain ⟨K, hK⟩ := (locallyLipschitz_shiftedMoment_succ (j-k-1)).locallyLipschitzOn
    |>.exists_lipschitzOnWith_of_compact (s := uIcc a b) isCompact_uIcc
  exact hK.absolutelyContinuousOnInterval

theorem ae_off_thetaKnots (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ x ∂μ, ∀ n : ℕ, 0 < n → x ≠ thetaKnot n := by
  have hn := (Set.countable_range thetaKnot).ae_notMem μ
  exact hn.mono fun x hx n _ h => hx ⟨n, h.symm⟩

/-- The last initial Wronskian is positive almost everywhere on the
central interval, where its last derivative can jump at a theta knot. -/
theorem eventually_lastShiftedMomentWronskian_pos_ae :
    ∀ᶠ r : ℕ in atTop, ∀ p : ℕ, 1 ≤ p → p ≤ r →
      ∀ᵐ u ∂volume.restrict (Ioc 0 (shiftCriticalCutoff r)),
        0 < shiftedMomentWronskian (2*r-p) p u := by
  filter_upwards [eventually_shiftedMomentWronskian_pos] with r hr p hp hpr
  filter_upwards [ae_off_thetaKnots (volume.restrict (Ioc 0 (shiftCriticalCutoff r))),
    ae_restrict_mem measurableSet_Ioc] with u hkn hu
  exact hr p p hp le_rfl hpr u hu.1 hu.2 hkn

#print axioms contDiffAt_shiftedMoment_off_knots
#print axioms contDiff_shiftedMoment_of_lt
#print axioms absolutelyContinuousOnInterval_iteratedDeriv_shiftedMoment
#print axioms eventually_lastShiftedMomentWronskian_pos_ae

end Nuttall
