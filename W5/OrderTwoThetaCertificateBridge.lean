import W5.NormalizedKernelFirstOrder
import W5.AnalyticTargets
import W5.Range

/-!
# The genuine order-two determinant and the numerical theta matrix

The factorization of the original `W 2` has been established by
`normalizedMatrixTwo_det_exact`. This module isolates exactly the
remaining analytic/numerical obligations for turning that identity
into its strict sign: identification of four theta coefficients
and a strict sign of the theta matrix determinant.

None of the sign hypotheses below is asserted unconditionally.
-/

namespace W5

/-- The 2 x 2 leading principal block of the independently defined
theta coefficient matrix. -/
noncomputable def thetaMatrixTwo (x : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of (fun i j =>
    thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)

/-- The analytic/numerical identification required for order two
only; no coefficients of order two through four are assumed. -/
def OrderTwoThetaIdentification (x : ℝ) : Prop :=
  ∀ i j : Fin 2,
    analyticCoeff x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
      thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- Entrywise agreement produces equality of the genuine and the
numerical order-two matrices. -/
theorem normalizedMatrixTwo_eq_thetaMatrixTwo (x : ℝ)
    (h : OrderTwoThetaIdentification x) :
    normalizedMatrixTwo x = thetaMatrixTwo x := by
  apply Matrix.ext
  intro i j
  exact h i j

/-- The repository's full 5 x 5 transform assumption implies
the strictly weaker order-two identification. -/
theorem orderTwoThetaIdentification_of_transform (x : ℝ)
    (hx : 0 < x) (hxb : x ≤ (145 : ℝ) / 256)
    (h : thetaTransformCorrect) : OrderTwoThetaIdentification x := by
  intro i j
  exact h x hx hxb ⟨i.val, by omega⟩ ⟨j.val, by omega⟩

/-- With exactly the four entries identified, the sign of the
numerical leading minor is equivalent to the original Wronskian sign.
There is NO assumption about the sign on either side. -/
theorem thetaMatrixTwo_negative_iff_W_two_negative (t : ℝ)
    (ht : 0 ≤ t) (h : OrderTwoThetaIdentification (xOfT t)) :
    (thetaMatrixTwo (xOfT t)).det < 0 ↔ W 2 t < 0 := by
  rw [← normalizedMatrixTwo_eq_thetaMatrixTwo (xOfT t) h]
  exact normalizedMatrixTwo_negative_iff_W_two_negative_exact t ht

/-- A certificate for the 2 x 2 theta determinant and the
four entrywise identities suffices for the true W2 sign. -/
theorem W_two_negative_of_orderTwo_certificate (t : ℝ) (ht : 0 ≤ t)
    (hident : OrderTwoThetaIdentification (xOfT t))
    (hdet : (thetaMatrixTwo (xOfT t)).det < 0) :
    W 2 t < 0 :=
  (thetaMatrixTwo_negative_iff_W_two_negative t ht hident).mp hdet

/-- Compatibility with the previously defined *conditional*
full analytical transform and matrix-sign goals.

In particular, this theorem does not establish either hypothesis. -/
theorem W_two_negative_of_full_theta_targets
    (hident : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive)
    (t : ℝ) (ht : 0 ≤ t) : W 2 t < 0 := by
  have hx := xOfT_positive_and_bounded t ht
  have hsmall : OrderTwoThetaIdentification (xOfT t) :=
    orderTwoThetaIdentification_of_transform
      (xOfT t) hx.1 hx.2 hident
  have hdet : (thetaMatrixTwo (xOfT t)).det < 0 :=
    (hsigns (xOfT t) hx.1 hx.2).2.1
  exact W_two_negative_of_orderTwo_certificate t ht hsmall hdet

end W5
