import W5.NormalizedKernelFirstOrder

/-!
# Order-three theta normalization: the exact triangular coordinate matrix

The genuine normalized kernel factors as a positive scalar times
`G(u) G(v) Psi1(t + S(u) + S(v))`. The Taylor coefficients of the
one-variable functions G and S to degree two suggest the explicit
triangular matrix `normalizedCoordinateMatrixThree`.

This file proves the *matrix algebra* of the 3-by-3 transformation,
including its exact determinant scaling. The assertion identifying
all the genuine analytic Taylor coefficients with this congruence
remains the explicit `OrderThreeNormalizedJetData` hypothesis.

No Wronskian sign assumption and no `sorry` are used.
-/

namespace W5

/-- The quadratic coefficient of exp(u/x)/(1+x*u)^(5/4).
For the intended interpretation, x is strictly positive. -/
noncomputable def secondGaugeCoeff (x : ℝ) : ℝ :=
  1 / (2 * x ^ 2) - (5 : ℝ) / 4 + 45 * x ^ 2 / 32

/-- The quadratic coefficient of log(1+x*u)/4. -/
noncomputable def secondShiftCoeff (x : ℝ) : ℝ :=
  -(x ^ 2) / 8

/-- The degree-two coordinate/gauge Taylor matrix. Its rows are
(1,0,0), (a,b,0), (alpha,a*b+beta,b^2/2) with
a=G'(0), b=S'(0), alpha=[u^2]G, beta=[u^2]S. -/
noncomputable def normalizedCoordinateMatrixThree (x : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    if i.val = 0 then
      if j.val = 0 then 1 else 0
    else if i.val = 1 then
      if j.val = 0 then firstGaugeSlope x
      else if j.val = 1 then firstShiftSlope x else 0
    else
      if j.val = 0 then secondGaugeCoeff x
      else if j.val = 1 then
        firstGaugeSlope x * firstShiftSlope x + secondShiftCoeff x
      else firstShiftSlope x ^ 2 / 2

/-- Exactly the three entries above the diagonal vanish. -/
theorem normalizedCoordinateMatrixThree_above_diag_zero (x : ℝ) :
    normalizedCoordinateMatrixThree x 0 1 = 0 ∧
    normalizedCoordinateMatrixThree x 0 2 = 0 ∧
    normalizedCoordinateMatrixThree x 1 2 = 0 := by
  simp [normalizedCoordinateMatrixThree]

/-- The triangular determinant does not depend on the gauge
coefficients: it is b^3 / 2, where b=x/4. -/
theorem normalizedCoordinateMatrixThree_det (x : ℝ) :
    (normalizedCoordinateMatrixThree x).det =
      firstShiftSlope x ^ 3 / 2 := by
  rw [Matrix.det_fin_three]
  simp [normalizedCoordinateMatrixThree]
  ring

/-- Positivity of all diagonal entries along the genuine theta ray. -/
theorem normalizedCoordinateMatrixThree_diag_pos
    (x : ℝ) (hx : 0 < x) :
    ∀ i : Fin 3, 0 < normalizedCoordinateMatrixThree x i i := by
  intro i
  have hb : 0 < firstShiftSlope x := by
    dsimp [firstShiftSlope]
    positivity
  fin_cases i
  · norm_num [normalizedCoordinateMatrixThree]
  · simpa [normalizedCoordinateMatrixThree] using hb
  · have hb2 : 0 < firstShiftSlope x ^ 2 / 2 := by positivity
    simpa [normalizedCoordinateMatrixThree] using hb2

/-- Genuine normalized mixed-derivative matrix of order three. -/
noncomputable def normalizedMatrixThree (x : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j =>
    analyticCoeff x ⟨i.val, by omega⟩ ⟨j.val, by omega⟩)

/-- The remaining genuine order-three analytic obligation:
identify the 3-by-3 mixed Taylor-jet matrix with the explicitly
given triangular change of coordinates. This is a hypothesis,
NOT a claimed theorem. -/
def OrderThreeNormalizedJetData (x : ℝ) : Prop :=
  normalizedMatrixThree x =
    kernelNormalization x •
      (normalizedCoordinateMatrixThree x *
        Matrix.of (fun (i j : Fin 3) =>
          iteratedDeriv (i.val + j.val) Psi1 (thetaTimeOfX x)) *
        (normalizedCoordinateMatrixThree x).transpose)

/-- Exact order-three determinant scaling, conditional ONLY on
the explicit mixed-jet matrix identity above.
In particular, the scaling is positive when x>0. -/
theorem normalizedMatrixThree_det_of_jet
    (x : ℝ) (h : OrderThreeNormalizedJetData x) :
    (normalizedMatrixThree x).det =
      kernelNormalization x ^ 3 *
        (firstShiftSlope x ^ 6 / 4) *
          W 3 (thetaTimeOfX x) := by
  rw [h, Matrix.det_smul, det_of_congruence, Fintype.card_fin,
    normalizedCoordinateMatrixThree_det]
  change kernelNormalization x ^ 3 *
      ((firstShiftSlope x ^ 3 / 2) ^ 2 *
        (Matrix.of (fun (i j : Fin 3) =>
          iteratedDeriv (i.val + j.val) Psi1 (thetaTimeOfX x))).det) =
    kernelNormalization x ^ 3 *
      (firstShiftSlope x ^ 6 / 4) *
        (Matrix.of (fun (i j : Fin 3) =>
          iteratedDeriv (i.val + j.val) Psi1 (thetaTimeOfX x))).det
  ring

/-- Sign transfer for the actual third Wronskian on the theta ray.
The mixed Taylor jet identity is the explicit unresolved premise. -/
theorem normalizedMatrixThree_negative_iff_W_three_negative_of_jet
    (t : ℝ) (ht : 0 ≤ t)
    (hjet : OrderThreeNormalizedJetData (xOfT t)) :
    (normalizedMatrixThree (xOfT t)).det < 0 ↔ W 3 t < 0 := by
  rw [normalizedMatrixThree_det_of_jet (xOfT t) hjet,
    thetaTimeOfX_xOfT]
  have hx : 0 < xOfT t := (xOfT_positive_and_bounded t ht).1
  have hc : 0 < kernelNormalization (xOfT t) :=
    kernelNormalization_pos (xOfT t) hx
  have hb : 0 < firstShiftSlope (xOfT t) := by
    dsimp [firstShiftSlope]
    positivity
  have hfactor :
      0 < kernelNormalization (xOfT t) ^ 3 *
        (firstShiftSlope (xOfT t) ^ 6 / 4) := by
    positivity
  constructor
  · intro hneg
    by_contra hn
    have hw : 0 ≤ W 3 t := le_of_not_gt hn
    have hnonneg : 0 ≤
        (kernelNormalization (xOfT t) ^ 3 *
          (firstShiftSlope (xOfT t) ^ 6 / 4)) * W 3 t :=
      mul_nonneg hfactor.le hw
    linarith
  · intro hw
    exact mul_neg_of_pos_of_neg hfactor hw

/-!
## Full sign and zero transfer at order three

The analytic mixed-jet identity is kept explicit. Once established,
the strictly positive determinant multiplier preserves all three
possible signs, not only strict negativity.
-/

/-- The exact determinant multiplier on the theta ray is positive. -/
theorem normalizedThreeMultiplier_pos
    (t : ℝ) (ht : 0 ≤ t) :
    0 < kernelNormalization (xOfT t) ^ 3 *
      (firstShiftSlope (xOfT t) ^ 6 / 4) := by
  have hx : 0 < xOfT t := (xOfT_positive_and_bounded t ht).1
  have hc : 0 < kernelNormalization (xOfT t) :=
    kernelNormalization_pos (xOfT t) hx
  have hb : 0 < firstShiftSlope (xOfT t) := by
    dsimp [firstShiftSlope]
    positivity
  positivity

/-- The normalized determinant is positive exactly when W3 is. -/
theorem normalizedMatrixThree_positive_iff_W_three_positive_of_jet
    (t : ℝ) (ht : 0 ≤ t)
    (hjet : OrderThreeNormalizedJetData (xOfT t)) :
    0 < (normalizedMatrixThree (xOfT t)).det ↔ 0 < W 3 t := by
  rw [normalizedMatrixThree_det_of_jet (xOfT t) hjet,
    thetaTimeOfX_xOfT]
  exact (mul_pos_iff_of_pos_left (normalizedThreeMultiplier_pos t ht))

/-- A zero of the genuine W3 is exactly a zero of the normalized
order-three determinant, provided the analytic jet identity holds. -/
theorem normalizedMatrixThree_zero_iff_W_three_zero_of_jet
    (t : ℝ) (ht : 0 ≤ t)
    (hjet : OrderThreeNormalizedJetData (xOfT t)) :
    (normalizedMatrixThree (xOfT t)).det = 0 ↔ W 3 t = 0 := by
  rw [normalizedMatrixThree_det_of_jet (xOfT t) hjet,
    thetaTimeOfX_xOfT]
  exact mul_eq_zero_iff_of_ne_zero_left
    (ne_of_gt (normalizedThreeMultiplier_pos t ht))

/-- The complete trichotomy is transported by the exact positive
normalization, with no assumption about the determinant sign. -/
theorem normalizedMatrixThree_sign_trichotomy_of_jet
    (t : ℝ) (ht : 0 ≤ t)
    (hjet : OrderThreeNormalizedJetData (xOfT t)) :
    ((normalizedMatrixThree (xOfT t)).det < 0 ↔ W 3 t < 0) ∧
    ((normalizedMatrixThree (xOfT t)).det = 0 ↔ W 3 t = 0) ∧
    (0 < (normalizedMatrixThree (xOfT t)).det ↔ 0 < W 3 t) := by
  exact ⟨normalizedMatrixThree_negative_iff_W_three_negative_of_jet
      t ht hjet,
    normalizedMatrixThree_zero_iff_W_three_zero_of_jet t ht hjet,
    normalizedMatrixThree_positive_iff_W_three_positive_of_jet
      t ht hjet⟩

end W5
