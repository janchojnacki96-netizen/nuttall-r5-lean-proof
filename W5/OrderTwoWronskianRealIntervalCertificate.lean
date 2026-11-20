import W5.ThetaActualLeadingMinorOneTwoFromPivots
import W5.OrderTwoThetaCertificateBridge

/-!
# Direct order-two ORIGINAL Nuttall Wronskian sign from a real interval certificate

The repository already proved the genuine analytic identity
`thetaMatrixTwo_negative_iff_W_two_negative`, assuming entrywise
identification between analyticCoeff and thetaCoefficient.

The new PR #97 proves that a certified 5x5 REAL theta matrix
gives a strictly negative TRUE thetaMatrixTwo determinant.

This module composes these prior results to derive the sign of
the ORIGINAL order-two Wronskian W 2 t, not a numerical surrogate.

Exactly two outstanding kinds of premises remain visible:
1. the original theta transformation (full or just four
   order-two coefficient identities);
2. the 25 REAL entry enclosures plus the finite five-pivot
   rational interval sign checks.

No assumptions about the determinant itself are made.
-/

namespace W5

/-- From the actual theta order-two coefficient identities
and one exact interval certificate, deduce the ORIGINAL
Wronskian order-two sign. -/
theorem W_two_negative_of_real_theta_interval_certificate
    (t : ℝ) (ht : 0 ≤ t)
    (hident : OrderTwoThetaIdentification (xOfT t))
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j)
        (thetaCoefficient (xOfT t) i j))
    (hchecks : intervalLDL5Alternating B) :
    W 2 t < 0 := by
  exact W_two_negative_of_orderTwo_certificate t ht hident
    (thetaMatrixTwo_det_negative_of_interval
      (xOfT t) B hentry hchecks)

/-- The full unproved `thetaTransformCorrect` condition,
if eventually established, automatically supplies the four
coefficient identities for order two. This avoids requiring
a separate order-two change-of-variables proof. -/
theorem W_two_negative_of_transform_and_real_theta_interval
    (htransform : thetaTransformCorrect)
    (t : ℝ) (ht : 0 ≤ t)
    (B : Matrix (Fin 5) (Fin 5) QInterval)
    (hentry : ∀ i j : Fin 5,
      QInterval.ContainsReal (B i j)
        (thetaCoefficient (xOfT t) i j))
    (hchecks : intervalLDL5Alternating B) :
    W 2 t < 0 := by
  have hx := xOfT_positive_and_bounded t ht
  have hident : OrderTwoThetaIdentification (xOfT t) :=
    orderTwoThetaIdentification_of_transform
      (xOfT t) hx.1 hx.2.le htransform
  exact W_two_negative_of_real_theta_interval_certificate
    t ht hident B hentry hchecks

end W5
