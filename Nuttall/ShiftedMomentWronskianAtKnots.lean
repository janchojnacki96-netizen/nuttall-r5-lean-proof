import Nuttall.ShiftedMomentKnotDerivative
import Nuttall.ShiftCriticalMargin

namespace Nuttall

open Filter
open scoped Matrix.Norms.L2Operator

/-- When the derivative orders leave at least one power, reversing the
columns gives the Hankel matrix also at the theta knots. -/
theorem signed_shiftedMomentWronskian_eq_hankel_of_lt {L k : ℕ} (hk : k < L) (u : ℝ) :
    (-1:ℝ)^(k*(k-1)/2)*shiftedMomentWronskian L k u =
      (shiftedMomentHankel (L+k-2) k u).det := by
  let A := Matrix.of (fun i j : Fin k => iteratedDeriv i.val (shiftedMoment (L+j.val-1)) u)
  have hmat : A.submatrix id Fin.revPerm = shiftedMomentHankel (L+k-2) k u := by
    ext i j
    have hi := i.isLt
    have hj := j.isLt
    simp only [A, Matrix.submatrix_apply, Matrix.of_apply, id_eq, Fin.revPerm_apply, Fin.val_rev,
      shiftedMomentHankel]
    rw [iteratedDeriv_shiftedMoment_of_lt (by omega)]
    congr 1
    omega
  have hsign : (((Equiv.Perm.sign (@Fin.revPerm k) : ℤˣ) : ℤ) : ℝ) =
      (-1:ℝ)^(k*(k-1)/2) := by
    rw [sign_revPerm]
    norm_num [Units.val_pow_eq_pow_val]
  change (-1:ℝ)^(k*(k-1)/2)*A.det = _
  rw [← hmat, Matrix.det_permute', hsign]

/-- When all entries needed by the Wronskian have positive moment indices,
its strict sign holds on the entire central interval. -/
theorem eventually_shiftedMomentWronskian_pos_at_knots :
    ∀ᶠ r : ℕ in atTop, ∀ p k : ℕ, 1 ≤ k → k ≤ p → p ≤ r → k < 2*r-p →
      ∀ u : ℝ, 0 < u → u ≤ shiftCriticalCutoff r →
        0 < shiftedMomentWronskian (2*r-p) k u := by
  have hroot : 1/Real.sqrt 2 ≤ 3/4 := by
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by norm_num : 0 < (2:ℝ)))).2
    have hb : (4/3:ℝ) ≤ Real.sqrt 2 := by
      apply (sq_le_sq₀ (by norm_num) (Real.sqrt_nonneg _)).1
      rw [Real.sq_sqrt (by norm_num : 0 ≤ (2:ℝ))]
      norm_num
    linarith
  filter_upwards [eventually_shiftCriticalMargin (1/8) (by norm_num)] with
    r hr p k hk hkp hpr hL u hu huB
  let L := 2*r-p
  let M := L+k-2
  have hMr : r-1 ≤ M := by dsimp [M, L]; omega
  have hdim : 2*(k-1) ≤ M := by dsimp [M, L]; omega
  have h := hr M k hMr (hkp.trans hpr) hdim u hu huB
  have hlt : ‖summedCorrectedShiftCore M k u-shiftSignMatrix k‖ < 1 := by
    linarith only [h, hroot]
  let ε := (-1:ℝ)^(k*(k-1)/2)
  have hε : ε*ε = 1 := by dsimp [ε]; rw [← mul_pow]; norm_num
  have hs : 0 < ε*(shiftedMomentHankel M k u).det :=
    (shiftedMomentHankel_weighted_det_pos_iff hdim hu ε).2
      (signed_det_pos_of_norm_sub_shiftSignMatrix_lt _ hlt)
  rw [show (shiftedMomentHankel M k u).det = ε*shiftedMomentWronskian L k u from
    (signed_shiftedMomentWronskian_eq_hankel_of_lt hL u).symm, ← mul_assoc, hε, one_mul] at hs
  exact hs

/-- Every proper initial Wronskian has the strict sign also at knots. -/
theorem eventually_initialShiftedMomentWronskian_pos :
    ∀ᶠ r : ℕ in atTop, ∀ p k : ℕ, 1 ≤ k → k < p → p ≤ r →
      ∀ u : ℝ, 0 < u → u ≤ shiftCriticalCutoff r →
        0 < shiftedMomentWronskian (2*r-p) k u := by
  filter_upwards [eventually_shiftedMomentWronskian_pos_at_knots] with r hr p k hk hkp hpr
  exact hr p k hk hkp.le hpr (by omega)

#print axioms signed_shiftedMomentWronskian_eq_hankel_of_lt
#print axioms eventually_initialShiftedMomentWronskian_pos

end Nuttall
