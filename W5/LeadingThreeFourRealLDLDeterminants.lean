import W5.ThetaActualFullFiveDeterminantFromInterval

/-!
# Leading 3×3 and 4×4 real determinants from full-matrix LDL pivots

Mathlib's one-step `Matrix.det_fromBlocks₁₁` theorem, already
packaged as `det_eq_first_pivot_mul_leadingSchurBlock`, is applied
recursively to the two leading principal blocks of a 5×5 matrix.

The exact pivots are those of the SAME `realLDL5` algorithm whose
soundness was already proved for rational interval inputs. No manual
determinant expansions and no assumption about matrix signs are used.
-/

namespace W5

/-- Actual leading principal 3×3 matrix of an arbitrary 5×5 real matrix. -/
noncomputable def leadingRealThree
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of (fun i j =>
    A (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- Actual leading principal 4×4 matrix of an arbitrary 5×5 real matrix. -/
noncomputable def leadingRealFour
    (A : Matrix (Fin 5) (Fin 5) ℝ) :
    Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.of (fun i j =>
    A (⟨i.val, by omega⟩ : Fin 5)
      (⟨j.val, by omega⟩ : Fin 5))

/-- The leading three determinant equals the first three verified
real-LDL pivots multiplied together, assuming the first two are nonzero. -/
theorem det_leading_three_eq_realLDL5_product
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h0 : (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) ≠ 0)
    (h1 : (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) ≠ 0) :
    (leadingRealThree A).det =
      (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) *
      (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) *
      (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) := by
  have ha : (leadingRealThree A) 0 0 ≠ 0 := by
    change A 0 0 ≠ 0
    simpa only [realLDL5_pivot_zero_eq_schur] using h0
  have hb : (leadingSchurBlock 2 (leadingRealThree A)) 0 0 ≠ 0 := by
    change (schurTail4 A) 0 0 ≠ 0
    simpa only [realLDL5_pivot_one_eq_schur] using h1
  have hfirst :=
    det_eq_first_pivot_mul_leadingSchurBlock 2 (leadingRealThree A) ha
  have hsecond :=
    det_eq_first_pivot_mul_leadingSchurBlock 1
      (leadingSchurBlock 2 (leadingRealThree A)) hb
  calc
    (leadingRealThree A).det =
        (leadingRealThree A) 0 0 *
          (leadingSchurBlock 2 (leadingRealThree A)).det := hfirst
    _ = (leadingRealThree A) 0 0 *
          (leadingSchurBlock 2 (leadingRealThree A)) 0 0 *
          (leadingSchurBlock 1
            (leadingSchurBlock 2 (leadingRealThree A))).det := by
          rw [hsecond]
          ring
    _ = (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) *
          (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) *
          (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) := by
          rw [Matrix.det_fin_one]
          rfl

/-- The leading four determinant equals the first four verified
real-LDL pivots multiplied together, assuming the first three are nonzero. -/
theorem det_leading_four_eq_realLDL5_product
    (A : Matrix (Fin 5) (Fin 5) ℝ)
    (h0 : (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) ≠ 0)
    (h1 : (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) ≠ 0)
    (h2 : (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) ≠ 0) :
    (leadingRealFour A).det =
      (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) *
      (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) *
      (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) *
      (realLDL5 A 3) (pivotIndexFive 3) (pivotIndexFive 3) := by
  have ha : (leadingRealFour A) 0 0 ≠ 0 := by
    change A 0 0 ≠ 0
    simpa only [realLDL5_pivot_zero_eq_schur] using h0
  have hb : (leadingSchurBlock 3 (leadingRealFour A)) 0 0 ≠ 0 := by
    change (schurTail4 A) 0 0 ≠ 0
    simpa only [realLDL5_pivot_one_eq_schur] using h1
  have hc : (leadingSchurBlock 2
      (leadingSchurBlock 3 (leadingRealFour A))) 0 0 ≠ 0 := by
    change (schurTail3 A) 0 0 ≠ 0
    simpa only [realLDL5_pivot_two_eq_schur] using h2
  have hfirst :=
    det_eq_first_pivot_mul_leadingSchurBlock 3 (leadingRealFour A) ha
  have hsecond :=
    det_eq_first_pivot_mul_leadingSchurBlock 2
      (leadingSchurBlock 3 (leadingRealFour A)) hb
  have hthird :=
    det_eq_first_pivot_mul_leadingSchurBlock 1
      (leadingSchurBlock 2 (leadingSchurBlock 3 (leadingRealFour A))) hc
  calc
    (leadingRealFour A).det =
        (leadingRealFour A) 0 0 *
          (leadingSchurBlock 3 (leadingRealFour A)).det := hfirst
    _ = (leadingRealFour A) 0 0 *
          (leadingSchurBlock 3 (leadingRealFour A)) 0 0 *
          (leadingSchurBlock 2
            (leadingSchurBlock 3 (leadingRealFour A))).det := by
          rw [hsecond]
          ring
    _ = (leadingRealFour A) 0 0 *
          (leadingSchurBlock 3 (leadingRealFour A)) 0 0 *
          (leadingSchurBlock 2
            (leadingSchurBlock 3 (leadingRealFour A))) 0 0 *
          (leadingSchurBlock 1 (leadingSchurBlock 2
            (leadingSchurBlock 3 (leadingRealFour A)))).det := by
          rw [hthird]
          ring
    _ = (realLDL5 A 0) (pivotIndexFive 0) (pivotIndexFive 0) *
          (realLDL5 A 1) (pivotIndexFive 1) (pivotIndexFive 1) *
          (realLDL5 A 2) (pivotIndexFive 2) (pivotIndexFive 2) *
          (realLDL5 A 3) (pivotIndexFive 3) (pivotIndexFive 3) := by
          rw [Matrix.det_fin_one]
          rfl

end W5
