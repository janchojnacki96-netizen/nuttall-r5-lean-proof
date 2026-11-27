import Nuttall.TailIntegrationByParts
import Nuttall.Literature.Andreief

namespace Nuttall

open MeasureTheory Set

/-- The first multiple-integral representation, with the signed derivatives
of the auxiliary theta series in the second determinant. -/
theorem signed_wronskian_eq_andreief_integral {p m : ℕ} (hm : 2*p ≤ m)
    (t : ℝ) (ht : 0 ≤ t) :
    (p.factorial : ℝ) * ((2 : ℝ)^p * ((-1 : ℝ)^(p*(p-1)/2) * wronskian (psi m) p t)) =
    ∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) =>
        tailMomentWeight (m-(p-1)+i.val-2) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySignedJet i.val (x j))).det
      ∂Measure.pi (fun _ => volume.restrict (Ici t)) := by
  rw [twice_pow_signed_wronskian_eq_separated_moments hm t ht]
  exact Literature.andreief (volume.restrict (Ici t))
    (fun i s => tailMomentWeight (m-(p-1)+i.val-2) (s-t))
    (fun j => auxiliarySignedJet j.val)
    (fun i j => weight_mul_signedJet_integrable (m-(p-1)+i.val-2) j.val ht)

#print axioms signed_wronskian_eq_andreief_integral

end Nuttall
