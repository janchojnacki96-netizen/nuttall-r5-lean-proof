import Nuttall.AuxiliarySeries

namespace Nuttall

open Filter
open scoped BigOperators Topology

/-- Expanding finite sums in the columns of a determinant corresponds to
choosing one summand for each column independently. -/
theorem det_sum_columns {p : ℕ} (S : Fin p → Finset ℕ) (f : Fin p → Fin p → ℕ → ℝ) :
    (Matrix.of (fun (i j : Fin p) => ∑ n ∈ S j, f i j n)).det =
      ∑ v ∈ Fintype.piFinset S,
        (Matrix.of (fun (i j : Fin p) => f i j (v j))).det := by
  simp only [Matrix.det_apply', Matrix.of_apply, Finset.prod_univ_sum, Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Pointwise convergence of truncated auxiliary derivative determinants.
Here `x j` is a node, so the sums in that node are grouped by column. -/
theorem tendsto_auxiliary_determinant_truncations {p : ℕ} (x : Fin p → ℝ) :
    Tendsto (fun N : ℕ => (Matrix.of (fun (i j : Fin p) =>
      ∑ n ∈ Finset.range N, auxiliaryWeightedSummand (auxiliaryDerivativePolynomial i.val) n (x j))).det)
      atTop (𝓝 ((Matrix.of (fun (i j : Fin p) => auxiliarySignedJet i.val (x j))).det)) := by
  let A (N : ℕ) : Matrix (Fin p) (Fin p) ℝ := Matrix.of (fun (i j : Fin p) =>
    ∑ n ∈ Finset.range N, auxiliaryWeightedSummand (auxiliaryDerivativePolynomial i.val) n (x j))
  let B : Matrix (Fin p) (Fin p) ℝ :=
    Matrix.of (fun (i j : Fin p) => auxiliarySignedJet i.val (x j))
  have h : Tendsto A atTop (𝓝 B) := by
    refine tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => ?_))
    exact (auxiliaryWeightedSummand_summable (auxiliaryDerivativePolynomial i.val) (x j)).hasSum.tendsto_sum_nat
  exact continuous_id.matrix_det.continuousAt.tendsto.comp h

#print axioms det_sum_columns
#print axioms tendsto_auxiliary_determinant_truncations

end Nuttall
