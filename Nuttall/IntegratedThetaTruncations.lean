import Nuttall.ThetaDeterminantTruncations
import Nuttall.TruncatedMomentConvergence

namespace Nuttall

open MeasureTheory Set
open scoped BigOperators

private theorem theta_pair_integrable (k j n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (fun s => tailMomentWeight k (s-t) *
      auxiliaryWeightedSummand (auxiliaryDerivativePolynomial j) n s) (Ici t) := by
  have h := (weighted_truncated_moment_integrable k j (n+1) ht).sub
    (weighted_truncated_moment_integrable k j n ht)
  have heq :
      (fun s => tailMomentWeight k (s-t) * auxiliarySignedJetTruncated j (n+1) s) -
        (fun s => tailMomentWeight k (s-t) * auxiliarySignedJetTruncated j n s) =
      fun s => tailMomentWeight k (s-t) *
        auxiliaryWeightedSummand (auxiliaryDerivativePolynomial j) n s := by
    funext s
    simp only [Pi.sub_apply, auxiliarySignedJetTruncated, Finset.sum_range_succ]
    ring
  rw [heq] at h
  exact h

/-- Each fixed tuple of theta indices has an absolutely integrable product
of determinants over the original orthant. -/
theorem integrable_theta_determinant_term {p : ℕ} (k n : Fin p → ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : Fin p → ℝ =>
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) =>
        auxiliaryWeightedSummand (auxiliaryDerivativePolynomial i.val) (n j) (x j))).det)
      (Measure.pi (fun _ => volume.restrict (Ici t))) := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.sum_mul, Finset.mul_sum]
  apply integrable_finsetSum
  intro σ _
  apply integrable_finsetSum
  intro τ _
  have h := Integrable.fintype_prod
    (fun j : Fin p => theta_pair_integrable (k (σ j)) (τ j).val (n j) ht)
  simp only [Finset.prod_mul_distrib] at h
  convert h.const_mul
    ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) * (((Equiv.Perm.sign τ : ℤˣ) : ℤ) : ℝ)) using 1
  funext x
  ring

/-- Andréief's integral with finite theta cutoffs is exactly the sum of the
integrals for individual tuples. -/
theorem integral_truncated_determinants_eq_sum {p : ℕ} (k : Fin p → ℕ) (N : ℕ)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) => auxiliarySignedJetTruncated i.val N (x j))).det
      ∂Measure.pi (fun _ => volume.restrict (Ici t))) =
    ∑ n ∈ Fintype.piFinset (fun _ : Fin p => Finset.range N),
      ∫ x : Fin p → ℝ,
      (Matrix.of (fun (i j : Fin p) => tailMomentWeight (k i) (x j-t))).det *
      (Matrix.of (fun (i j : Fin p) =>
        auxiliaryWeightedSummand (auxiliaryDerivativePolynomial i.val) (n j) (x j))).det
      ∂Measure.pi (fun _ => volume.restrict (Ici t)) := by
  simp_rw [auxiliarySignedJetTruncated, det_sum_columns, Finset.mul_sum]
  exact integral_finsetSum _ (fun n _ => integrable_theta_determinant_term k n ht)

#print axioms integral_truncated_determinants_eq_sum

end Nuttall
