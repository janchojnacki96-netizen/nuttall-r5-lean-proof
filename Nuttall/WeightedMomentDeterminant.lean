import Nuttall.SignedTailDeterminant
import Nuttall.TailMoments

namespace Nuttall

open MeasureTheory Set

/-- At level `m ≥ 2p` every entry in the reversed tail matrix is a
weighted moment. The factor `2^p` clears the halves in the entries. -/
theorem twice_pow_signed_wronskian_eq_moment_det {p m : ℕ} (hm : 2*p ≤ m)
    (t : ℝ) (ht : 0 ≤ t) :
    (2 : ℝ)^p * ((-1 : ℝ)^(p*(p-1)/2) * wronskian (psi m) p t) =
      (Matrix.of (fun (i j : Fin p) =>
        ∫ s in Ici t, tailMomentWeight (m-(p-1)+i.val-j.val-2) (s-t) * auxiliaryTheta s)).det := by
  rw [signed_wronskian_psi_eq_tail_det (by omega) t]
  let A : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of (fun (i j : Fin p) => psi (m-(p-1)+i.val-j.val) t)
  change (2 : ℝ)^p * A.det = _
  have hscale : (2 : ℝ)^p * A.det = ((2 : ℝ) • A).det := by
    rw [Matrix.det_smul, Fintype.card_fin]
  rw [hscale]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro i j
  have hj := j.isLt
  let k := m-(p-1)+i.val-j.val
  have hk : k-2+2 = k := by
    dsimp [k]
    omega
  change 2 * psi k t = ∫ s in Ici t, tailMomentWeight (k-2) (s-t) * auxiliaryTheta s
  simpa only [hk] using twice_psi_succ_succ_eq_weighted_moment (k-2) t ht

#print axioms twice_pow_signed_wronskian_eq_moment_det

end Nuttall
