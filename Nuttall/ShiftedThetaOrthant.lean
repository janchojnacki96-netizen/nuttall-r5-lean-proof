import Nuttall.ShiftedMomentCutoff
import Nuttall.ShiftedThetaIntegral
import Nuttall.AuxiliarySeries

namespace Nuttall

open MeasureTheory Set
open scoped BigOperators

/-- Product Lebesgue measure on the open positive orthant. -/
noncomputable def positiveOrthant (p : ℕ) : Measure (Fin p → ℝ) :=
  Measure.pi (fun _ => volume.restrict (Ioi (0 : ℝ)))

/-- Translate one tuple of theta indices to the common orthant. The
coordinate restrictions and the square-root denominators are in the columns. -/
theorem integral_fixed_indices_common_orthant {p : ℕ} (k n : Fin p → ℕ) (t : ℝ) :
    (∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) =>
        auxiliaryWeightedSummand (auxiliaryDerivativePolynomial i.val) (n j) (x j))).det
        ∂Measure.pi (fun _ => volume.restrict (Ici t))) =
    (thetaScale t * Real.exp t)^p * (4 * thetaScale t)^(p*(p-1)/2) *
      ∫ u : Fin p → ℝ,
        (Matrix.of (fun (i j : Fin p) => shiftedMomentTerm (k i) (n j) (u j))).det *
        (Matrix.vandermonde (fun j => Real.exp (4*u j))).det *
        (∏ j : Fin p, thetaOrthantWeight (thetaScale t) (u j)) ∂positiveOrthant p := by
  by_cases hn : ∀ j, 0 < n j
  · have ha (j : Fin p) : 0 ≤ thetaKnot (n j) := by
      apply div_nonneg (Real.log_nonneg _) (by norm_num)
      exact_mod_cast hn j
    change _ = _ * ∫ u, _ ∂Measure.pi (fun _ => volume.restrict (Ioi (0 : ℝ)))
    rw [auxiliaryWeightedSummand, integral_fixed_indices_shift k n hn t, ← product_tail_measure_open_eq_closed,
      ← product_tail_measure_restrict _ ha, ← integral_indicator (MeasurableSet.univ_pi
        (fun _ => measurableSet_Ioi))]
    congr 1
    apply integral_congr_ae
    filter_upwards with u
    rw [det_shiftedMomentTerm_eq_indicator k n hn]
    by_cases hu : u ∈ univ.pi (fun j => Ioi (thetaKnot (n j)))
    · rw [indicator_of_mem hu, indicator_of_mem hu]
      have hd :
          (Matrix.of (fun (i j : Fin p) =>
            tailMomentWeight (k i) (u j-thetaKnot (n j)) / Real.sqrt (n j : ℝ))).det =
          (∏ j : Fin p, (Real.sqrt (n j : ℝ))⁻¹) *
            (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (u j-thetaKnot (n j)))).det := by
        rw [← Matrix.det_mul_row]
        congr 1
        ext i j
        simp [div_eq_mul_inv, mul_comm]
      rw [hd]
      simp_rw [div_eq_mul_inv, Finset.prod_mul_distrib]
      ring
    · rw [indicator_of_notMem hu, indicator_of_notMem hu]
      simp
  · push Not at hn
    obtain ⟨j, hj⟩ := hn
    have hz : n j = 0 := Nat.eq_zero_of_le_zero hj
    have hleft (x : Fin p → ℝ) :
        (Matrix.of (fun (i j : Fin p) =>
          auxiliaryWeightedSummand (auxiliaryDerivativePolynomial i.val) (n j) (x j))).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero j
      intro i
      simp [hz, auxiliaryWeightedSummand, auxiliarySummand]
    have hright (u : Fin p → ℝ) :
        (Matrix.of (fun (i j : Fin p) => shiftedMomentTerm (k i) (n j) (u j))).det = 0 := by
      apply Matrix.det_eq_zero_of_column_eq_zero j
      intro i
      simp [hz, shiftedMomentTerm]
    simp [hleft, hright]

#print axioms integral_fixed_indices_common_orthant

end Nuttall
