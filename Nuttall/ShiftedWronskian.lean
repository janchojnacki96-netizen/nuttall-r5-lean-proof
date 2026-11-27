import Nuttall.ShiftedOrthantConvergence
import Nuttall.IntegratedThetaTruncations

namespace Nuttall

open MeasureTheory Set Filter
open scoped BigOperators Topology

private theorem integral_shiftedOrthant_truncated_eq_sum {p : ℕ} {X : ℝ}
    (hX : 0 < X) (k : Fin p → ℕ) (N : ℕ) :
    (∫ u, shiftedOrthantIntegrand X (fun i _ => shiftedMomentTruncated (k i) N) u
      ∂positiveOrthant p) =
    ∑ n ∈ Fintype.piFinset (fun _ : Fin p => Finset.range N),
      ∫ u, shiftedOrthantIntegrand X (fun i j => shiftedMomentTerm (k i) (n j)) u
        ∂positiveOrthant p := by
  simp_rw [shiftedOrthantIntegrand, shiftedMomentTruncated, det_sum_columns, Finset.sum_mul]
  exact integral_finsetSum _ (fun n _ => integrable_shiftedOrthant_term hX k n)

theorem andreief_integral_eq_shifted {p : ℕ} (k : Fin p → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySignedJet i.val (x j))).det
      ∂Measure.pi (fun _ => volume.restrict (Ici t))) =
    (thetaScale t * Real.exp t)^p * (4 * thetaScale t)^(p*(p-1)/2) *
      ∫ u, shiftedOrthantIntegrand (thetaScale t) (fun i _ => shiftedMoment (k i)) u
        ∂positiveOrthant p := by
  have hX : 0 < thetaScale t := mul_pos Real.pi_pos (Real.exp_pos _)
  apply tendsto_nhds_unique (tendsto_truncated_andreief k ht)
  refine ((tendsto_shiftedOrthant_integral hX k).const_mul _).congr' ?_
  filter_upwards with N
  rw [integral_truncated_determinants_eq_sum k N ht, integral_shiftedOrthant_truncated_eq_sum hX,
    Finset.mul_sum]
  exact Finset.sum_congr rfl (fun n _ => (integral_fixed_indices_common_orthant k n t).symm)

/-- The exact normalization in equation eq:anorm of Section 4.1.
The matrix of shifted moments is transposed, which leaves its determinant unchanged. -/
theorem signed_wronskian_eq_shifted_orthant {p m : ℕ} (hp : 1 ≤ p) (hm : 2*p ≤ m)
    (t : ℝ) (ht : 0 ≤ t) :
    (-1 : ℝ)^(p*(p-1)/2) * wronskian (psi m) p t =
    ((thetaScale t * Real.exp t / 2)^p * (4 * thetaScale t)^(p*(p-1)/2) / p.factorial) *
      ∫ u, shiftedOrthantIntegrand (thetaScale t) (fun (i _ : Fin p) =>
        shiftedMoment (m-p+i.val-1)) u ∂positiveOrthant p := by
  have hk (i : Fin p) : m-(p-1)+i.val-2 = m-p+i.val-1 := by omega
  have h := signed_wronskian_eq_andreief_integral hm t ht
  rw [andreief_integral_eq_shifted _ ht] at h
  simp only [hk] at h
  have hfac : (p.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero p
  have hpow : (2 : ℝ)^p ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [div_pow]
  field_simp
  linear_combination h

/-- The signed Wronskian has the sign of the full shifted integral. -/
theorem signed_wronskian_pos_iff_shifted_orthant {p m : ℕ} (hp : 1 ≤ p) (hm : 2*p ≤ m)
    (t : ℝ) (ht : 0 ≤ t) :
    (0 < (-1 : ℝ)^(p*(p-1)/2) * wronskian (psi m) p t) ↔
      0 < ∫ u, shiftedOrthantIntegrand (thetaScale t) (fun (i _ : Fin p) =>
        shiftedMoment (m-p+i.val-1)) u ∂positiveOrthant p := by
  rw [signed_wronskian_eq_shifted_orthant hp hm t ht]
  apply mul_pos_iff_of_pos_left
  unfold thetaScale
  positivity

#print axioms andreief_integral_eq_shifted
#print axioms signed_wronskian_eq_shifted_orthant
#print axioms signed_wronskian_pos_iff_shifted_orthant

end Nuttall
