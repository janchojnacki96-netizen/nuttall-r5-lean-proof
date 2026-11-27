import Nuttall.ShiftHankelCongruence
import Nuttall.SignedTailDeterminant

namespace Nuttall

/-- The ordinary order-(k) Wronskian of the first (k) shifted moments,
with derivative orders indexing the rows. -/
noncomputable def shiftedMomentWronskian (L k : ℕ) (u : ℝ) : ℝ :=
  (Matrix.of (fun i j : Fin k =>
    iteratedDeriv i.val (shiftedMoment (L+j.val-1)) u)).det

theorem signed_shiftedMomentWronskian_eq_hankel {L k : ℕ} (hL : k ≤ L) {u : ℝ}
    (hu : ∀ n : ℕ, 0 < n → u ≠ thetaKnot n) :
    (-1 : ℝ)^(k*(k-1)/2) * shiftedMomentWronskian L k u =
      (shiftedMomentHankel (L+k-2) k u).det := by
  let A := Matrix.of (fun i j : Fin k => iteratedDeriv i.val (shiftedMoment (L+j.val-1)) u)
  have hmat : A.submatrix id Fin.revPerm = shiftedMomentHankel (L+k-2) k u :=
    shiftedMoment_wronskian_reverse_columns hL hu
  have hsign : (((Equiv.Perm.sign (@Fin.revPerm k) : ℤˣ) : ℤ) : ℝ) =
      (-1 : ℝ)^(k*(k-1)/2) := by
    rw [sign_revPerm]
    norm_num [Units.val_pow_eq_pow_val]
  change (-1 : ℝ)^(k*(k-1)/2) * A.det = _
  rw [← hmat, Matrix.det_permute', hsign]

/-- Positivity of the ordinary moment Wronskian is the determinant
test for the corrected matrix with the sign of the column reversal. -/
theorem shiftedMomentWronskian_pos_iff {L k : ℕ} (hL : k ≤ L) {u : ℝ}
    (hu₀ : 0 < u) (hu : ∀ n : ℕ, 0 < n → u ≠ thetaKnot n) :
    0 < shiftedMomentWronskian L k u ↔
      0 < (-1 : ℝ)^(k*(k-1)/2) * (summedCorrectedShiftCore (L+k-2) k u).det := by
  let ε := (-1 : ℝ)^(k*(k-1)/2)
  have hε : ε*ε = 1 := by
    dsimp [ε]
    rw [← mul_pow]
    norm_num
  have hW : shiftedMomentWronskian L k u = ε * (shiftedMomentHankel (L+k-2) k u).det := by
    rw [← signed_shiftedMomentWronskian_eq_hankel hL hu]
    change _ = ε * (ε * shiftedMomentWronskian L k u)
    rw [← mul_assoc, hε, one_mul]
  rw [hW]
  exact shiftedMomentHankel_weighted_det_pos_iff (by omega) hu₀ ε

#print axioms signed_shiftedMomentWronskian_eq_hankel
#print axioms shiftedMomentWronskian_pos_iff

end Nuttall
