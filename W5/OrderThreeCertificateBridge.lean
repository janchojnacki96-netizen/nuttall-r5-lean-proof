import W5.NormalizedKernelEdgeSymmetry
import W5.OrderTwoCertificateBridge

/-!
# Connecting the genuine order-three normalized determinant to the certificate

The equality with the certificate's theta coefficient matrix uses
`thetaTransformCorrect`, which has NOT yet been proved.
The relation between the genuine normalized order-three matrix and
the original Wronskian uses `OrderThreeNormalizedJetData`, also not
yet established. Both hypotheses remain explicit in the resulting
sign theorems. Nothing in this file proves the conjectured signs.
-/

namespace W5

/-- Pointwise equality of the genuine order-three normalized matrix
with the proposed theta coefficient matrix, under the explicit
theta transformation hypothesis. -/
theorem normalizedMatrixThree_eq_thetaMatrix_of_transform
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256)
    (htransform : thetaTransformCorrect) :
    normalizedMatrixThree x =
      Matrix.of (fun (i j : Fin 3) =>
        thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  apply Matrix.ext
  intro i j
  change analyticCoeff x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
    thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  exact htransform x hx hbound _ _

/-- The certificate's third determinant sign transfers to the
actual normalized matrix, conditional on the analytic transform. -/
theorem normalizedMatrixThree_negative_of_theta_certificate
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256)
    (htransform : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive) :
    (normalizedMatrixThree x).det < 0 := by
  rw [normalizedMatrixThree_eq_thetaMatrix_of_transform
    x hx hbound htransform]
  exact (hsigns x hx hbound).2.2.1

/-- Explicit three-premise reduction of the original W3 sign:
theta transform, proposed certificate signs, and genuine mixed jets. -/
theorem W_three_negative_of_theta_certificate
    (htransform : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive)
    (t : ℝ) (ht : 0 ≤ t)
    (hjet : OrderThreeNormalizedJetData (xOfT t)) :
    W 3 t < 0 := by
  obtain ⟨hx, hbound⟩ := xOfT_positive_and_bounded t ht
  have hdet : (normalizedMatrixThree (xOfT t)).det < 0 :=
    normalizedMatrixThree_negative_of_theta_certificate
      (xOfT t) hx hbound.le htransform hsigns
  exact (normalizedMatrixThree_negative_iff_W_three_negative_of_jet
    t ht hjet).mp hdet

/-- Under explicitly listed outstanding proof obligations,
the first three signs in the original Nuttall statement hold. -/
theorem first_three_nuttall_signs_of_theta_certificate
    (htransform : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive)
    (hjet : ∀ t : ℝ, 0 ≤ t →
      OrderThreeNormalizedJetData (xOfT t)) :
    ∀ t : ℝ, 0 ≤ t →
      0 < W 1 t ∧ W 2 t < 0 ∧ W 3 t < 0 := by
  intro t ht
  exact ⟨W_one_pos t ht,
    W_two_negative_of_theta_certificate htransform hsigns t ht,
    W_three_negative_of_theta_certificate
      htransform hsigns t ht (hjet t ht)⟩

end W5
