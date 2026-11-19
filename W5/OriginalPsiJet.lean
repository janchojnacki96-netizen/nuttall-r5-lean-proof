import W5.PhiSeventhDerivative

/-!
# Exact finite theta-jet matrix for the ORIGINAL Nuttall Wronskians

Each entry of the original Wronskian through size five is equal
to an explicitly convergent theta derivative series, by the
unconditional proofs of termwise differentiation through order seven.
This is NOT the normalized Taylor coefficient matrix in the numeric
certificate, and does not establish any determinant sign.
-/

namespace W5

/-- Genuine derivative jet of Psi1, explicitly represented for orders 0–8. -/
noncomputable def originalPsiJet (k : ℕ) (t : ℝ) : ℝ :=
  match k with
  | 0 => Psi1 t
  | 1 => -Phi t
  | 2 => -(∑' n : ℕ, phiSummandDerivative n t)
  | 3 => -(∑' n : ℕ, phiSummandSecondDerivative n t)
  | 4 => -(∑' n : ℕ, phiSummandThirdDerivative n t)
  | 5 => -(∑' n : ℕ, phiSummandFourthDerivative n t)
  | 6 => -(∑' n : ℕ, phiSummandFifthDerivative n t)
  | 7 => -(∑' n : ℕ, phiSummandSixthDerivative n t)
  | 8 => -(∑' n : ℕ, phiSummandSeventhDerivative n t)
  | _ => 0

/-- Every order needed by Wronskians of size <= 5 agrees with the
original analytical derivative of the actual theta integral. -/
theorem originalPsiJet_eq_iteratedDeriv (k : ℕ) (t : ℝ)
    (hk : k ≤ 8) :
    originalPsiJet k t = iteratedDeriv k Psi1 t := by
  interval_cases k
  · simp [originalPsiJet]
  · simpa [originalPsiJet, iteratedDeriv_one] using (Psi1_deriv t).symm
  · simpa [originalPsiJet] using (Psi1_second_derivative t).symm
  · simpa [originalPsiJet] using (Psi1_third_derivative t).symm
  · simpa [originalPsiJet] using (Psi1_fourth_derivative t).symm
  · simpa [originalPsiJet] using (Psi1_fifth_derivative t).symm
  · simpa [originalPsiJet] using (Psi1_sixth_derivative t).symm
  · simpa [originalPsiJet] using (Psi1_seventh_derivative t).symm
  · simpa [originalPsiJet] using (Psi1_eighth_derivative t).symm

/-- EXACT determinant identity for the ORIGINAL Wronskian, r <= 5.
No sign assumptions, no numerical surrogate, no Taylor bridge assumptions. -/
theorem W_eq_originalPsiJet_det (r : ℕ) (hr : r ≤ 5) (t : ℝ) :
    W r t = (Matrix.of (fun (i j : Fin r) =>
        originalPsiJet (i.val + j.val) t)).det := by
  unfold W
  congr 1
  apply Matrix.ext
  intro i j
  have hij : i.val + j.val ≤ 8 := by
    have hi := i.isLt
    have hj := j.isLt
    omega
  simpa only [Matrix.of_apply] using
    (originalPsiJet_eq_iteratedDeriv (i.val + j.val) t hij).symm

/-- Original fifth Wronskian as an explicit theta derivative matrix.
This is an identity, NOT the strict positive sign theorem. -/
theorem W_five_eq_originalPsiJet_det (t : ℝ) :
    W 5 t = (Matrix.of (fun (i j : Fin 5) =>
        originalPsiJet (i.val + j.val) t)).det :=
  W_eq_originalPsiJet_det 5 (by omega) t

end W5
