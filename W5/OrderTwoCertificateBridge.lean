import W5.NormalizedKernelFirstOrder

/-!
# Conditional certificate interface for the genuine second Wronskian

The original analytic normalized two-by-two determinant has already
been proved equal to a strictly positive multiple of `W 2 t`.
This file connects that *unconditional* analytic identity to the
**separate, still unproved** theta-coefficient representation and
certified determinant sign propositions from `AnalyticTargets`.

No numerical sign result is assumed proven or declared as a primitive:
`thetaTransformCorrect` and `analyticMatrixPositive` remain
explicit premises. In particular, nothing here proves `MainClaim`.
-/

namespace W5

/-- If the proposed theta transform is correct, the original
normalized analytic matrix equals the numerical theta-coefficient
matrix at order two, entry by entry. -/
theorem normalizedMatrixTwo_eq_thetaMatrix_of_transform
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256)
    (htransform : thetaTransformCorrect) :
    normalizedMatrixTwo x =
      Matrix.of (fun (i j : Fin 2) =>
        thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩) := by
  apply Matrix.ext
  intro i j
  change analyticCoeff x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
    thetaCoefficient x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩
  exact htransform x hx hbound _ _

/-- Transport of the order-two *certificate* sign to the genuine
normalized Taylor matrix, with the two outstanding obligations explicit. -/
theorem normalizedMatrixTwo_negative_of_theta_certificate
    (x : ℝ) (hx : 0 < x) (hbound : x ≤ (145 : ℝ) / 256)
    (htransform : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive) :
    (normalizedMatrixTwo x).det < 0 := by
  rw [normalizedMatrixTwo_eq_thetaMatrix_of_transform
    x hx hbound htransform]
  exact (hsigns x hx hbound).2.1

/-- The actual second Nuttall sign follows from the as-yet-unproved
theta transform identity and numerical sign certification.
The normalization itself is now unconditional. -/
theorem W_two_negative_of_theta_certificate
    (htransform : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive)
    (t : ℝ) (ht : 0 ≤ t) :
    W 2 t < 0 := by
  obtain ⟨hx, hbound⟩ := xOfT_positive_and_bounded t ht
  have hdet : (normalizedMatrixTwo (xOfT t)).det < 0 :=
    normalizedMatrixTwo_negative_of_theta_certificate
      (xOfT t) hx hbound.le htransform hsigns
  exact (normalizedMatrixTwo_negative_iff_W_two_negative_exact t ht).mp hdet

/-- A compact reduction: under the full proposed certificate
hypotheses, the first TWO signs of the original MainClaim hold.
The last three are intentionally not asserted here. -/
theorem first_two_nuttall_signs_of_theta_certificate
    (htransform : thetaTransformCorrect)
    (hsigns : analyticMatrixPositive) :
    ∀ t : ℝ, 0 ≤ t → 0 < W 1 t ∧ W 2 t < 0 := by
  intro t ht
  exact ⟨W_one_pos t ht,
    W_two_negative_of_theta_certificate htransform hsigns t ht⟩

end W5
