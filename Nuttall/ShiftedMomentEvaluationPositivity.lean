import Nuttall.CentralEvaluationPositivity
import Nuttall.ShiftedMomentRegularity

namespace Nuttall

open Filter Set

/-- For all sufficiently large parent ranks, the evaluation determinant of the
shifted moments is positive for every smaller rank and every strictly ordered
choice of central nodes, including nodes that coincide with theta knots. -/
theorem eventually_shiftedMoment_evaluation_det_pos :
    ∀ᶠ r : ℕ in atTop, ∀ p : ℕ, 1 ≤ p → p ≤ r →
      ∀ u : Fin p → ℝ, StrictMono u → (∀ i, u i ∈ Ioo 0 (shiftCriticalCutoff r)) →
      0 < (Matrix.of (fun i j => shiftedMoment (2*r-p+j.val-1) (u i))).det := by
  filter_upwards [eventually_shiftedMomentWronskian_pos_at_knots,
    eventually_shiftedMomentWronskian_pos, eventually_ge_atTop (2:ℕ)] with
    r hkn hoff hr p hp hpr u hu huJ
  cases p with
  | zero => omega
  | succ n =>
    by_cases hn : n = 0
    · subst n
      rw [Matrix.det_fin_one]
      simpa [shiftedMomentWronskian, Matrix.det_fin_one] using
        hkn 1 1 le_rfl le_rfl hpr (by omega) (u 0) (huJ 0).1 (huJ 0).2.le
    · let f (j : Fin (n+1)) := shiftedMoment (2*r-(n+1)+j.val-1)
      let S := range thetaKnot
      change 0 < (Matrix.of (fun i j => f j (u i))).det
      apply det_eval_pos_of_familyWronskians (S := S) (countable_range thetaKnot) f _ _ _ _
        u hu huJ (fun h => (hn h).elim)
      · intro j m hm
        exact (contDiff_shiftedMoment_of_lt (j := 2*r-(n+1)+j.val-1) (by omega)).contDiffOn
      · intro j m hm
        have hidx : m < 2*r-(n+1)+j.val-1 := by omega
        show LocallyLipschitzOn _ (iteratedDeriv m (shiftedMoment (2*r-(n+1)+j.val-1)))
        rw [funext (iteratedDeriv_shiftedMoment_of_lt hidx),
          show 2*r-(n+1)+j.val-1-m = (2*r-(n+1)+j.val-1-m-1)+1 by omega]
        exact (locallyLipschitz_shiftedMoment_succ _).locallyLipschitzOn
      · intro j x hx hxS
        exact contDiffAt_shiftedMoment_off_knots _ (fun l _ heq => hxS ⟨l, heq.symm⟩)
      · intro k hk x hx hxS
        change 0 < shiftedMomentWronskian (2*r-(n+1)) (k+1) x
        by_cases hke : k = n
        · exact hoff (n+1) (k+1) (by omega) (by omega) hpr x hx.1 hx.2.le
            (fun l _ heq => hxS hke ⟨l, heq.symm⟩)
        · exact hkn (n+1) (k+1) (by omega) (by omega) hpr (by omega) x hx.1 hx.2.le

#print axioms eventually_shiftedMoment_evaluation_det_pos

end Nuttall
